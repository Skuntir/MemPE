use std::borrow::Cow;

use pelite::PeFile;

use crate::pe::exports::ExportIndex;
use crate::pe::image::{read_pointer, read_u16, read_u32, write_u16, write_u32, write_u64};
use crate::pe::imports::{ImportGroup, ImportPlan, build_plan};
use crate::pe::parse::{parse_disk_image, parse_memory_image};
use crate::pe::{
    EntryPointRva, IAT_DIRECTORY, IMAGE_SCN_MEM_EXECUTE, IMAGE_SCN_MEM_READ, IMAGE_SCN_MEM_WRITE,
    IMPORT_DIRECTORY, PeImage, PeKind, PeModel, RegionEvidence, Rva, SECURITY_DIRECTORY,
    SectionModel,
};
use crate::{AppError, AppResult};

const DOS_LFANEW_OFFSET: usize = 0x3c;
const SECTION_HEADER_SIZE: usize = 40;
const MAX_OUTPUT_SIZE: usize = 1024 * 1024 * 1024;
const DEBUG_DIRECTORY: usize = 6;
const EXCEPTION_DIRECTORY: usize = 3;
const MAX_DISK_HEADERS: usize = 1024 * 1024;
const RUNTIME_FUNCTION_SIZE: usize = 12;
const IMPORT_DESCRIPTOR_SIZE: usize = 20;
const BASERELOC_DIRECTORY: usize = 5;
const RELOCATION_BLOCK_HEADER: usize = 8;
const RELOCATION_ABSOLUTE: u16 = 0;
const RELOCATION_HIGHLOW: u16 = 3;
const RELOCATION_DIR64: u16 = 10;
const MAX_RELOCATION_BLOCKS: usize = 65_536;
const TLS_DIRECTORY: usize = 9;
const DEBUG_ENTRY_SIZE: usize = 28;
const DEBUG_ENTRY_RAW_RVA: usize = 20;
const DEBUG_ENTRY_RAW_POINTER: usize = 24;
const MAX_DEBUG_ENTRIES: usize = 256;
const IMAGE_DLLCHARACTERISTICS_DYNAMIC_BASE: u16 = 0x0040;
const MAX_TLS_CALLBACKS: usize = 1_024;
const SECTION_NAME_SIZE: usize = 8;
const PRINTABLE_FIRST: u8 = 0x20;
const PRINTABLE_LAST: u8 = 0x7e;
const MEMPE_IMPORT_CHARACTERISTICS: u32 = 0xC000_0040;
const IMAGE_SCN_CNT_CODE: u32 = 0x0000_0020;
const IMAGE_SCN_CNT_INITIALIZED_DATA: u32 = 0x0000_0040;
const IMAGE_SCN_CNT_UNINITIALIZED_DATA: u32 = 0x0000_0080;
const PAGE_SIZE: usize = 4 * 1024;
const PAGE_RESIDENT: u8 = 0b01;
const PAGE_PRIVATE: u8 = 0b10;
const HIGH_ENTROPY_THRESHOLD: f64 = 7.2;
const MIN_ENTROPY_SECTION_BYTES: usize = 1024;
const MIN_ABSENT_SECTION_BYTES: usize = 1024;
const ENTROPY_ALPHABET: usize = 256;
const BOUND_IMPORT_DIRECTORY: usize = 11;
const DIRECTORY_COUNT: usize = 16;
const DIRECTORY_NAMES: [&str; DIRECTORY_COUNT] = [
    "Export",
    "Import",
    "Resource",
    "Exception",
    "Certificate",
    "BaseReloc",
    "Debug",
    "Architecture",
    "GlobalPtr",
    "TLS",
    "LoadConfig",
    "BoundImport",
    "IAT",
    "DelayImport",
    "COMDescriptor",
    "Reserved",
];
const ROUTINE_DIRECTORIES: [usize; 2] = [SECURITY_DIRECTORY, BOUND_IMPORT_DIRECTORY];
const IMAGE_FILE_EXECUTABLE_IMAGE: u16 = 0x0002;
const FILE_CHARACTERISTICS_OFFSET: usize = 22;
const CHECKSUM_WORD_SIZE: usize = 2;
const MAX_CHECKSUM_WORDS: usize = MAX_OUTPUT_SIZE / CHECKSUM_WORD_SIZE;

pub(crate) struct RebuiltImage {
    pub(crate) bytes: Vec<u8>,
    pub(crate) kind: PeKind,
    pub(crate) is_dll: bool,
    pub(crate) section_count: usize,
    pub(crate) salvaged_headers: bool,
    pub(crate) disk_headers_used: bool,
    pub(crate) cleared_directories: usize,
    pub(crate) invalid_unwind_entries: usize,
    pub(crate) imports_rebuilt: usize,
    pub(crate) unresolved_delay: usize,
    pub(crate) ambiguous_imports: usize,
    pub(crate) renamed_sections: usize,
    pub(crate) tls_callbacks: usize,
    pub(crate) entry_point: u32,
    pub(crate) entry_section: Option<String>,
    pub(crate) repaired_debug_entries: usize,
    pub(crate) fixed_image_base: bool,
    pub(crate) notable_cleared_directories: Vec<String>,
    pub(crate) executable_flag_added: bool,
    pub(crate) entry_unwind_covered: Option<bool>,
    pub(crate) write_execute_sections: usize,
    pub(crate) never_decrypted_sections: usize,
    pub(crate) absent_sections: usize,
}

struct SectionLayout<'a> {
    model: &'a SectionModel,
    source_length: usize,
    raw_offset: usize,
    raw_size: usize,
}

pub(crate) fn rebuild(
    memory: &[u8],
    regions: &[RegionEvidence],
    observed_base: usize,
    disk_headers: Option<&[u8]>,
    exports: &ExportIndex,
    entry_point: Option<EntryPointRva>,
    page_flags: &[u8],
) -> AppResult<RebuiltImage> {
    let (source, disk_headers_used) = resolve_source_bytes(memory, regions, disk_headers)?;
    let image = parse_memory_image(&source)
        .map_err(|error| AppError::new(format!("rebuilt PE headers are invalid: {error}")))?;
    let memory = image.bytes();
    let model = image.model();
    let (mut output, layouts, header_size) = build_output_buffer(model, memory)?;

    write_core_header_fields(&mut output, model, observed_base, header_size)?;
    let renamed_sections = write_sections(&mut output, memory, &layouts)?;

    let mut repairs = apply_repairs(&mut output, model, &layouts, header_size)?;
    let (import_plan, written) = resolve_imports(
        &mut output,
        model,
        &image,
        observed_base,
        exports,
        &mut repairs,
    )?;
    let (final_entry_point, executable_flag_added) =
        finalize_output(&mut output, model, entry_point)?;

    Ok(RebuiltImage {
        bytes: output,
        kind: model.kind,
        is_dll: model.is_dll,
        section_count: model.sections.len().saturating_add(usize::from(written)),
        salvaged_headers: model.salvaged,
        disk_headers_used,
        cleared_directories: repairs.cleared.total,
        notable_cleared_directories: names_to_strings(&repairs.cleared.notable),
        invalid_unwind_entries: repairs.invalid_unwind_entries,
        imports_rebuilt: if written { import_plan.recovered } else { 0 },
        unresolved_delay: import_plan.unresolved_delay,
        ambiguous_imports: import_plan.ambiguous,
        renamed_sections,
        tls_callbacks: count_tls_callbacks(&image, observed_base),
        entry_point: final_entry_point,
        entry_section: entry_section_name(&layouts, final_entry_point),
        repaired_debug_entries: repairs.repaired_debug_entries,
        fixed_image_base: repairs.fixed_image_base,
        executable_flag_added,
        entry_unwind_covered: entry_unwind_covered(&repairs.unwind_ranges, final_entry_point),
        write_execute_sections: count_write_execute_sections(&layouts, regions),
        never_decrypted_sections: never_decrypted_sections(memory, &layouts, page_flags),
        absent_sections: absent_sections(memory, &layouts),
    })
}

fn resolve_source_bytes<'a>(
    memory: &'a [u8],
    regions: &[RegionEvidence],
    disk_headers: Option<&[u8]>,
) -> AppResult<(Cow<'a, [u8]>, bool)> {
    let (initial, disk_headers_used) = match parse_memory_image(memory) {
        Ok(_) => (Cow::Borrowed(memory), false),
        Err(memory_error) => {
            let Some(disk_headers) = disk_headers else {
                return Err(memory_error);
            };
            let repaired = merge_header_evidence(memory, disk_headers)?;
            parse_memory_image(&repaired).map_err(|disk_error| {
                AppError::new(format!(
                    "memory headers are invalid ({memory_error}); disk header repair failed ({disk_error})"
                ))
            })?;
            (Cow::Owned(repaired), true)
        }
    };
    let recovered = {
        let image = parse_memory_image(&initial)?;
        recover_section_headers(image.bytes(), image.model(), regions)?
    };
    let resolved = match recovered {
        Some(bytes) => Cow::Owned(bytes),
        None => initial,
    };
    Ok((resolved, disk_headers_used))
}

fn build_output_buffer<'a>(
    model: &'a PeModel,
    memory: &[u8],
) -> AppResult<(Vec<u8>, Vec<SectionLayout<'a>>, usize)> {
    let section_table_end = model
        .sections
        .last()
        .map(|section| section.header_offset.saturating_add(SECTION_HEADER_SIZE))
        .ok_or_else(|| AppError::new("PE has no section headers"))?;
    let header_size = align_up(section_table_end, model.file_alignment as usize)?;
    let layouts = layout_sections(model, memory.len(), header_size)?;
    let output_size = layouts
        .iter()
        .map(|layout| layout.raw_offset.saturating_add(layout.raw_size))
        .max()
        .unwrap_or(header_size)
        .max(header_size);
    if output_size > MAX_OUTPUT_SIZE {
        return Err(AppError::new(
            "rebuilt PE exceeds the 1 GiB output safety limit",
        ));
    }
    let mut output = Vec::new();
    output
        .try_reserve_exact(output_size)
        .map_err(|_| AppError::new("not enough memory for the rebuilt PE"))?;
    output.resize(output_size, 0);
    let copied_headers = header_size.min(memory.len());
    output[..copied_headers].copy_from_slice(&memory[..copied_headers]);
    Ok((output, layouts, header_size))
}

#[derive(Default)]
struct ClearedDirectories {
    total: usize,
    notable: Vec<&'static str>,
}

impl ClearedDirectories {
    fn record(&mut self, index: usize) {
        self.total = self.total.saturating_add(1);
        if is_notable_directory(index) {
            self.notable.push(directory_name(index));
        }
    }
}

fn directory_name(index: usize) -> &'static str {
    DIRECTORY_NAMES.get(index).copied().unwrap_or("Unknown")
}

fn is_notable_directory(index: usize) -> bool {
    !ROUTINE_DIRECTORIES.contains(&index)
}

fn names_to_strings(names: &[&'static str]) -> Vec<String> {
    names.iter().map(|name| (*name).to_string()).collect()
}

struct RepairStats {
    cleared: ClearedDirectories,
    unwind_ranges: Option<UnwindRanges>,
    invalid_unwind_entries: usize,
    repaired_debug_entries: usize,
    fixed_image_base: bool,
}

fn apply_repairs(
    output: &mut [u8],
    model: &PeModel,
    layouts: &[SectionLayout<'_>],
    header_size: usize,
) -> AppResult<RepairStats> {
    let cleared = clear_bad_directories(output, model, layouts, header_size)?;
    let exception = repair_exception_directory(output, model, layouts, header_size)?;
    let repaired_debug_entries = repair_debug_directory(output, model, layouts, header_size)?;
    let fixed_image_base = clear_dynamic_base(output, model)?;
    Ok(RepairStats {
        cleared,
        unwind_ranges: exception.ranges,
        invalid_unwind_entries: exception.invalid,
        repaired_debug_entries,
        fixed_image_base,
    })
}

fn resolve_imports(
    output: &mut Vec<u8>,
    model: &PeModel,
    image: &PeImage<'_>,
    observed_base: usize,
    exports: &ExportIndex,
    repairs: &mut RepairStats,
) -> AppResult<(ImportPlan, bool)> {
    let import_plan = build_plan(image, observed_base, exports);
    let (written, iat_cleared) = if import_plan.groups.is_empty() {
        (false, false)
    } else {
        append_import_section(output, model, &import_plan)?
    };
    if iat_cleared {
        repairs.cleared.record(IAT_DIRECTORY);
    }
    if !written && import_plan.existing.is_empty() {
        let extra = clear_directory(output, model, IMPORT_DIRECTORY)?;
        if extra > 0 {
            repairs.cleared.record(IMPORT_DIRECTORY);
        }
    }
    Ok((import_plan, written))
}

fn finalize_output(
    output: &mut Vec<u8>,
    model: &PeModel,
    entry_point: Option<EntryPointRva>,
) -> AppResult<(u32, bool)> {
    apply_entry_point(output, model, entry_point)?;
    write_derived_header_fields(output, model)?;
    let executable_flag_added = ensure_executable_image_flag(output, model)?;
    apply_checksum(output, model)?;
    let final_entry_point = read_u32(output, model.entry_point_offset)?;
    PeFile::from_bytes(output).map_err(|error| {
        AppError::new(format!("rebuilt PE failed independent reparse: {error}"))
    })?;
    Ok((final_entry_point, executable_flag_added))
}

fn ensure_executable_image_flag(output: &mut [u8], model: &PeModel) -> AppResult<bool> {
    let offset = model.nt_offset.saturating_add(FILE_CHARACTERISTICS_OFFSET);
    let characteristics = read_u16(output, offset)?;
    if characteristics & IMAGE_FILE_EXECUTABLE_IMAGE != 0 {
        return Ok(false);
    }
    write_u16(
        output,
        offset,
        characteristics | IMAGE_FILE_EXECUTABLE_IMAGE,
    )?;
    Ok(true)
}

fn apply_checksum(output: &mut [u8], model: &PeModel) -> AppResult<()> {
    let checksum_offset = model.size_of_headers_offset.saturating_add(4);
    write_u32(output, checksum_offset, 0)?;
    let checksum = compute_checksum(output)?;
    write_u32(output, checksum_offset, checksum)
}

fn compute_checksum(bytes: &[u8]) -> AppResult<u32> {
    let mut sum: u64 = 0;
    let mut offset = 0usize;
    for _word in 0..MAX_CHECKSUM_WORDS {
        if offset.saturating_add(CHECKSUM_WORD_SIZE) > bytes.len() {
            break;
        }
        sum = sum.saturating_add(u64::from(read_u16(bytes, offset)?));
        sum = (sum & 0xFFFF).saturating_add(sum >> 16);
        offset = offset.saturating_add(CHECKSUM_WORD_SIZE);
    }
    if !bytes.len().is_multiple_of(CHECKSUM_WORD_SIZE) {
        let last = *bytes.get(bytes.len().saturating_sub(1)).unwrap_or(&0);
        sum = sum.saturating_add(u64::from(last));
        sum = (sum & 0xFFFF).saturating_add(sum >> 16);
    }
    sum = (sum & 0xFFFF).saturating_add(sum >> 16);
    let folded = (sum & 0xFFFF).saturating_add(bytes.len() as u64);
    u32::try_from(folded).map_err(|_| AppError::new("checksum overflowed a PE field"))
}

fn write_core_header_fields(
    output: &mut [u8],
    model: &PeModel,
    observed_base: usize,
    header_size: usize,
) -> AppResult<()> {
    write_u16(output, 0, 0x5A4D)?;
    write_u32(
        output,
        DOS_LFANEW_OFFSET,
        u32::try_from(model.nt_offset)
            .map_err(|_| AppError::new("NT header offset does not fit a PE field"))?,
    )?;
    write_image_base(output, model, observed_base)?;
    write_u32(
        output,
        model.size_of_image_offset,
        rebuilt_image_size(model)?,
    )?;
    write_u32(
        output,
        model.size_of_headers_offset,
        u32::try_from(header_size)
            .map_err(|_| AppError::new("rebuilt header size does not fit a PE field"))?,
    )?;
    write_u32(
        output,
        model.number_of_directories_offset,
        u32::try_from(model.directory_count)
            .map_err(|_| AppError::new("directory count does not fit a PE field"))?,
    )
}

fn write_sections(
    output: &mut [u8],
    memory: &[u8],
    layouts: &[SectionLayout<'_>],
) -> AppResult<usize> {
    let mut renamed = 0usize;
    for (index, layout) in layouts.iter().enumerate() {
        let header = layout.model.header_offset;
        if let Some(name) = readable_section_name(layout.model.name(), index.saturating_add(1)) {
            output
                .get_mut(header..header.saturating_add(SECTION_NAME_SIZE))
                .ok_or_else(|| AppError::new("section name lies outside the rebuilt PE"))?
                .copy_from_slice(&name);
            renamed = renamed.saturating_add(1);
        }
        write_u32(
            output,
            header.saturating_add(16),
            u32::try_from(layout.raw_size)
                .map_err(|_| AppError::new("section raw size does not fit a PE field"))?,
        )?;
        write_u32(
            output,
            header.saturating_add(20),
            u32::try_from(layout.raw_offset)
                .map_err(|_| AppError::new("section file offset does not fit a PE field"))?,
        )?;
        let source_offset = layout.model.virtual_address.get() as usize;
        let source_end = source_offset
            .checked_add(layout.source_length)
            .ok_or_else(|| AppError::new("section source range overflowed"))?;
        let destination_end = layout
            .raw_offset
            .checked_add(layout.source_length)
            .ok_or_else(|| AppError::new("section output range overflowed"))?;
        let source = memory
            .get(source_offset..source_end)
            .ok_or_else(|| AppError::new("section source range is outside captured memory"))?;
        output
            .get_mut(layout.raw_offset..destination_end)
            .ok_or_else(|| AppError::new("section output range is outside rebuilt PE"))?
            .copy_from_slice(source);
    }
    Ok(renamed)
}

fn recover_section_headers(
    memory: &[u8],
    model: &PeModel,
    regions: &[RegionEvidence],
) -> AppResult<Option<Vec<u8>>> {
    if regions.is_empty() {
        return Ok(None);
    }
    let mut sections = model.sections.iter().collect::<Vec<_>>();
    sections.sort_unstable_by_key(|section| section.virtual_address);
    let mut recovered = None;
    let mut image_end = model.image_size as usize;
    for (index, section) in sections.iter().enumerate() {
        let start = section.virtual_address.get() as usize;
        let limit = sections
            .get(index + 1)
            .map(|next| next.virtual_address.get() as usize)
            .unwrap_or(memory.len())
            .min(memory.len());
        if start >= limit {
            continue;
        }
        let declared = section.virtual_size.max(section.raw_size) as usize;
        let expanded = expanded_section_length(memory, regions, start, limit, declared);
        let section_end = start.saturating_add(expanded).min(limit);
        let characteristics =
            recovered_characteristics(section.characteristics, regions, start, section_end);
        if expanded > declared {
            let virtual_size = u32::try_from(expanded)
                .map_err(|_| AppError::new("recovered section size exceeds u32"))?;
            let output = recovered.get_or_insert_with(|| memory.to_vec());
            write_u32(
                output,
                section.header_offset.saturating_add(8),
                virtual_size,
            )?;
            image_end = image_end.max(start.saturating_add(expanded));
        }
        if characteristics != section.characteristics {
            let output = recovered.get_or_insert_with(|| memory.to_vec());
            write_u32(
                output,
                section.header_offset.saturating_add(36),
                characteristics,
            )?;
        }
    }
    if image_end > model.image_size as usize {
        let image_size = align_up(image_end, model.section_alignment as usize)?;
        let image_size = u32::try_from(image_size)
            .map_err(|_| AppError::new("recovered image size exceeds u32"))?;
        let output = recovered.get_or_insert_with(|| memory.to_vec());
        write_u32(output, model.size_of_image_offset, image_size)?;
    }
    Ok(recovered)
}

fn expanded_section_length(
    memory: &[u8],
    regions: &[RegionEvidence],
    start: usize,
    limit: usize,
    declared: usize,
) -> usize {
    let scan_start = start.saturating_add(declared).min(limit);
    let mut last_byte = scan_start;
    for region in regions.iter().filter(|region| region.readable) {
        let region_end = region.offset.saturating_add(region.size);
        let range_start = scan_start.max(region.offset);
        let range_end = limit.min(region_end).min(memory.len());
        if range_start >= range_end {
            continue;
        }
        let Some(bytes) = memory.get(range_start..range_end) else {
            continue;
        };
        if let Some(index) = bytes.iter().rposition(|byte| *byte != 0) {
            last_byte = last_byte.max(range_start.saturating_add(index).saturating_add(1));
        }
    }
    last_byte.saturating_sub(start).max(declared)
}

fn recovered_characteristics(
    characteristics: u32,
    regions: &[RegionEvidence],
    start: usize,
    end: usize,
) -> u32 {
    let coverage = ProtectionCoverage::measure(regions, start, end);
    let mut recovered = characteristics;
    if coverage.executable > 0 {
        recovered |= IMAGE_SCN_MEM_EXECUTE | IMAGE_SCN_CNT_CODE;
    }
    if coverage.readable > 0 {
        recovered |= IMAGE_SCN_MEM_READ;
    }
    if coverage.write_is_substantial(end.saturating_sub(start)) {
        recovered |= IMAGE_SCN_MEM_WRITE;
    }
    recovered
}

#[derive(Default)]
struct ProtectionCoverage {
    committed: usize,
    readable: usize,
    writable: usize,
    executable: usize,
}

impl ProtectionCoverage {
    fn measure(regions: &[RegionEvidence], start: usize, end: usize) -> Self {
        let mut coverage = Self::default();
        for region in regions {
            let region_end = region.offset.saturating_add(region.size);
            let overlap_start = start.max(region.offset);
            let overlap_end = end.min(region_end);
            let bytes = overlap_end.saturating_sub(overlap_start);
            if bytes == 0 {
                continue;
            }
            coverage.committed = coverage.committed.saturating_add(bytes);
            if region.readable {
                coverage.readable = coverage.readable.saturating_add(bytes);
            }
            if region.writable {
                coverage.writable = coverage.writable.saturating_add(bytes);
            }
            if region.executable {
                coverage.executable = coverage.executable.saturating_add(bytes);
            }
        }
        coverage
    }

    fn write_is_substantial(&self, section_size: usize) -> bool {
        if self.committed == 0 || self.writable == 0 {
            return false;
        }
        let unanimous = self.writable >= section_size && self.committed >= section_size;
        let substantial = self.writable >= PAGE_SIZE.saturating_mul(2)
            && self.writable.saturating_mul(2) >= section_size;
        unanimous || substantial
    }
}

fn layout_sections<'a>(
    model: &'a PeModel,
    memory_size: usize,
    header_size: usize,
) -> AppResult<Vec<SectionLayout<'a>>> {
    let mut sections = model.sections.iter().collect::<Vec<_>>();
    sections.sort_unstable_by_key(|section| section.virtual_address);
    let mut layouts = Vec::with_capacity(sections.len());
    let mut raw_offset = header_size;
    for (index, section) in sections.iter().enumerate() {
        let source_offset = section.virtual_address.get() as usize;
        let declared_length = section.virtual_size.max(section.raw_size) as usize;
        let next_rva = sections
            .get(index + 1)
            .map(|next| next.virtual_address.get() as usize)
            .unwrap_or(memory_size);
        let until_next = next_rva.saturating_sub(source_offset);
        let available = memory_size.saturating_sub(source_offset);
        let source_length = declared_length.min(until_next).min(available);
        let raw_size = if source_length == 0 {
            0
        } else {
            align_up(source_length, model.file_alignment as usize)?
        };
        layouts.push(SectionLayout {
            model: section,
            source_length,
            raw_offset: if raw_size == 0 { 0 } else { raw_offset },
            raw_size,
        });
        raw_offset = raw_offset
            .checked_add(raw_size)
            .ok_or_else(|| AppError::new("rebuilt section layout overflowed"))?;
    }
    Ok(layouts)
}

fn rebuilt_image_size(model: &PeModel) -> AppResult<u32> {
    let maximum_end = model
        .sections
        .iter()
        .map(|section| {
            u64::from(section.virtual_address.get())
                + u64::from(section.virtual_size.max(section.raw_size))
        })
        .max()
        .unwrap_or(0);
    let aligned = align_up_u64(maximum_end, u64::from(model.section_alignment))?;
    u32::try_from(aligned).map_err(|_| AppError::new("rebuilt image size exceeds u32"))
}

fn write_image_base(output: &mut [u8], model: &PeModel, observed_base: usize) -> AppResult<()> {
    match model.kind {
        PeKind::Pe32 => write_u32(
            output,
            model.image_base_offset,
            u32::try_from(observed_base)
                .map_err(|_| AppError::new("observed PE32 image base exceeds 32 bits"))?,
        ),
        PeKind::Pe32Plus => write_u64(output, model.image_base_offset, observed_base as u64),
    }
}

fn clear_bad_directories(
    output: &mut [u8],
    model: &PeModel,
    layouts: &[SectionLayout<'_>],
    header_size: usize,
) -> AppResult<ClearedDirectories> {
    let mut cleared = ClearedDirectories::default();
    for index in 0..model.directory_count {
        let entry_offset = model
            .directory_offset(index)?
            .ok_or_else(|| AppError::new("data-directory slot is missing"))?;
        let rva = read_u32(output, entry_offset)?;
        let size = read_u32(output, entry_offset.saturating_add(4))?;
        if rva == 0 && size == 0 {
            continue;
        }
        let valid = index != SECURITY_DIRECTORY
            && directory_is_mapped(rva, size, layouts, header_size)
            && (index != BASERELOC_DIRECTORY
                || relocations_are_walkable(output, model, layouts, header_size, rva, size));
        if !valid {
            write_u32(output, entry_offset, 0)?;
            write_u32(output, entry_offset.saturating_add(4), 0)?;
            cleared.record(index);
        }
    }
    Ok(cleared)
}

fn relocations_are_walkable(
    output: &[u8],
    model: &PeModel,
    layouts: &[SectionLayout<'_>],
    header_size: usize,
    rva: u32,
    size: u32,
) -> bool {
    let Some(start) = rva_to_file(rva, layouts, header_size) else {
        return false;
    };
    let end = start.saturating_add(size as usize);
    let expected = match model.kind {
        PeKind::Pe32 => RELOCATION_HIGHLOW,
        PeKind::Pe32Plus => RELOCATION_DIR64,
    };
    let mut cursor = start;
    let mut fixups = 0usize;
    for _block in 0..MAX_RELOCATION_BLOCKS {
        if cursor >= end {
            return fixups > 0;
        }
        let (Ok(page), Ok(block_size)) = (
            read_u32(output, cursor),
            read_u32(output, cursor.saturating_add(4)),
        ) else {
            return false;
        };
        let block_size = block_size as usize;
        if block_size < RELOCATION_BLOCK_HEADER
            || !block_size.is_multiple_of(2)
            || cursor.saturating_add(block_size) > end
            || rva_to_file(page, layouts, header_size).is_none()
        {
            return false;
        }
        for index in 0..block_size.saturating_sub(RELOCATION_BLOCK_HEADER) / 2 {
            let offset = cursor
                .saturating_add(RELOCATION_BLOCK_HEADER)
                .saturating_add(index.saturating_mul(2));
            let Ok(entry) = read_u16(output, offset) else {
                return false;
            };
            let kind = entry >> 12;
            if kind == RELOCATION_ABSOLUTE {
                continue;
            }
            if kind != expected {
                return false;
            }
            fixups = fixups.saturating_add(1);
        }
        cursor = cursor.saturating_add(block_size);
    }
    false
}

fn merge_header_evidence(memory: &[u8], disk: &[u8]) -> AppResult<Vec<u8>> {
    let disk_image = parse_disk_image(disk)?;
    let model = disk_image.model();
    let memory_entry_point = validate_header_evidence(memory, model)?;
    let header_size = disk_header_size(disk, model)?;
    if header_size > memory.len() {
        return Err(AppError::new(
            "disk PE headers are larger than the captured image",
        ));
    }
    let mut repaired = memory.to_vec();
    let source = disk
        .get(..header_size)
        .ok_or_else(|| AppError::new("disk PE headers are truncated"))?;
    let destination = repaired
        .get_mut(..header_size)
        .ok_or_else(|| AppError::new("captured PE header range is missing"))?;
    destination.copy_from_slice(source);
    if let Some(entry_point) = memory_entry_point {
        write_u32(&mut repaired, model.entry_point_offset, entry_point)?;
    }
    Ok(repaired)
}

fn validate_header_evidence(memory: &[u8], model: &PeModel) -> AppResult<Option<u32>> {
    if model.image_size as usize > memory.len() {
        return Err(AppError::new("disk SizeOfImage exceeds the captured image"));
    }
    let memory_machine = read_u16(memory, model.nt_offset.saturating_add(4)).unwrap_or(0);
    let disk_machine = match model.kind {
        PeKind::Pe32 => 0x014C,
        PeKind::Pe32Plus => 0x8664,
    };
    if matches!(memory_machine, 0x014C | 0x8664) && memory_machine != disk_machine {
        return Err(AppError::new(
            "disk headers conflict with the captured image architecture",
        ));
    }
    let memory_magic = read_u16(memory, model.entry_point_offset.saturating_sub(16)).unwrap_or(0);
    let disk_magic = match model.kind {
        PeKind::Pe32 => 0x010B,
        PeKind::Pe32Plus => 0x020B,
    };
    if matches!(memory_magic, 0x010B | 0x020B) && memory_magic != disk_magic {
        return Err(AppError::new(
            "disk headers conflict with the captured optional-header format",
        ));
    }
    let matching_structure = memory_machine == disk_machine || memory_magic == disk_magic;
    let entry_point = read_u32(memory, model.entry_point_offset)
        .ok()
        .filter(|rva| matching_structure && model.executable_rva(Rva(*rva)));
    Ok(entry_point)
}

fn disk_header_size(disk: &[u8], model: &PeModel) -> AppResult<usize> {
    let section_table_end = model
        .sections
        .last()
        .and_then(|section| section.header_offset.checked_add(SECTION_HEADER_SIZE))
        .ok_or_else(|| AppError::new("disk PE has no complete section table"))?;
    let size = align_up(section_table_end, model.file_alignment as usize)?;
    if size > MAX_DISK_HEADERS || size > disk.len() {
        return Err(AppError::new(
            "disk PE header size is outside the 1 MiB safety limit",
        ));
    }
    Ok(size)
}

fn apply_entry_point(
    output: &mut [u8],
    model: &PeModel,
    entry_point: Option<EntryPointRva>,
) -> AppResult<()> {
    let Some(entry_point) = entry_point else {
        return Ok(());
    };
    let rva = Rva(entry_point.get());
    if !model.executable_rva(rva) {
        return Err(AppError::new(format!(
            "manual entry point RVA 0x{:X} is not inside an executable section",
            entry_point.get()
        )));
    }
    write_u32(output, model.entry_point_offset, entry_point.get())
}

fn write_derived_header_fields(output: &mut [u8], model: &PeModel) -> AppResult<()> {
    let section_count = usize::from(read_u16(output, model.nt_offset.saturating_add(6))?);
    let maximum_section_count = model.sections.len().saturating_add(1);
    if section_count < model.sections.len() || section_count > maximum_section_count {
        return Err(AppError::new("rebuilt PE has an invalid section count"));
    }
    let first_section = model
        .sections
        .first()
        .map(|section| section.header_offset)
        .ok_or_else(|| AppError::new("rebuilt PE has no section table"))?;
    let mut sizes = DerivedSizes::default();
    for index in 0..section_count {
        let offset = first_section
            .checked_add(index.saturating_mul(SECTION_HEADER_SIZE))
            .ok_or_else(|| AppError::new("rebuilt section header offset overflowed"))?;
        sizes.add_section(output, offset, model.file_alignment)?;
    }
    write_u32(output, model.size_of_code_offset, sizes.code)?;
    write_u32(
        output,
        model.size_of_initialized_data_offset,
        sizes.initialized_data,
    )?;
    write_u32(
        output,
        model.size_of_uninitialized_data_offset,
        sizes.uninitialized_data,
    )?;
    write_u32(output, model.base_of_code_offset, sizes.base_of_code)
}

#[derive(Default)]
struct DerivedSizes {
    code: u32,
    initialized_data: u32,
    uninitialized_data: u32,
    base_of_code: u32,
}

impl DerivedSizes {
    fn add_section(&mut self, output: &[u8], offset: usize, file_alignment: u32) -> AppResult<()> {
        let virtual_size = read_u32(output, offset.saturating_add(8))?;
        let virtual_address = read_u32(output, offset.saturating_add(12))?;
        let raw_size = read_u32(output, offset.saturating_add(16))?;
        let characteristics = read_u32(output, offset.saturating_add(36))?;
        if characteristics & IMAGE_SCN_CNT_CODE != 0 {
            self.code = add_size(self.code, raw_size, "code size")?;
            if self.base_of_code == 0 || virtual_address < self.base_of_code {
                self.base_of_code = virtual_address;
            }
        }
        if characteristics & IMAGE_SCN_CNT_INITIALIZED_DATA != 0 {
            self.initialized_data =
                add_size(self.initialized_data, raw_size, "initialized-data size")?;
        }
        if characteristics & IMAGE_SCN_CNT_UNINITIALIZED_DATA != 0 {
            let aligned = align_up_u64(u64::from(virtual_size), u64::from(file_alignment))?;
            let aligned = u32::try_from(aligned)
                .map_err(|_| AppError::new("uninitialized-data size exceeds u32"))?;
            self.uninitialized_data =
                add_size(self.uninitialized_data, aligned, "uninitialized-data size")?;
        }
        Ok(())
    }
}

fn add_size(left: u32, right: u32, name: &str) -> AppResult<u32> {
    left.checked_add(right)
        .ok_or_else(|| AppError::new(format!("{name} overflowed")))
}

fn repair_exception_directory(
    output: &mut [u8],
    model: &PeModel,
    layouts: &[SectionLayout<'_>],
    header_size: usize,
) -> AppResult<ExceptionRepair> {
    if model.kind != PeKind::Pe32Plus || EXCEPTION_DIRECTORY >= model.directory_count {
        return Ok(ExceptionRepair::absent());
    }
    let entry_offset = model
        .directory_offset(EXCEPTION_DIRECTORY)?
        .ok_or_else(|| AppError::new("exception-directory slot is missing"))?;
    let rva = read_u32(output, entry_offset)?;
    let size = read_u32(output, entry_offset.saturating_add(4))? as usize;
    if rva == 0 || size == 0 {
        return Ok(ExceptionRepair::absent());
    }
    let Some(file_offset) = rva_to_file(rva, layouts, header_size) else {
        return Ok(ExceptionRepair::absent());
    };
    let scan =
        collect_valid_runtime_functions(output, model, layouts, header_size, file_offset, size)?;
    let ranges = runtime_function_ranges(&scan.valid);
    if scan.invalid == 0 {
        return Ok(ExceptionRepair {
            invalid: 0,
            ranges: Some(ranges),
        });
    }
    write_valid_runtime_functions(output, entry_offset, file_offset, size, &scan.valid)?;
    Ok(ExceptionRepair {
        invalid: scan.invalid,
        ranges: Some(ranges),
    })
}

type UnwindRanges = Vec<(u32, u32)>;

struct ExceptionRepair {
    invalid: usize,
    ranges: Option<UnwindRanges>,
}

impl ExceptionRepair {
    fn absent() -> Self {
        Self {
            invalid: 0,
            ranges: None,
        }
    }
}

struct ExceptionScan {
    valid: Vec<[u8; RUNTIME_FUNCTION_SIZE]>,
    invalid: usize,
}

fn collect_valid_runtime_functions(
    output: &[u8],
    model: &PeModel,
    layouts: &[SectionLayout<'_>],
    header_size: usize,
    file_offset: usize,
    size: usize,
) -> AppResult<ExceptionScan> {
    let count = size / RUNTIME_FUNCTION_SIZE;
    let mut valid = Vec::<[u8; RUNTIME_FUNCTION_SIZE]>::with_capacity(count);
    let mut invalid = usize::from(!size.is_multiple_of(RUNTIME_FUNCTION_SIZE));
    for index in 0..count {
        let offset = file_offset
            .checked_add(index.saturating_mul(RUNTIME_FUNCTION_SIZE))
            .ok_or_else(|| AppError::new("runtime-function offset overflowed"))?;
        let Some(entry) = output.get(offset..offset.saturating_add(RUNTIME_FUNCTION_SIZE)) else {
            invalid = invalid.saturating_add(count.saturating_sub(index));
            break;
        };
        if runtime_function_is_valid(output, entry, model, layouts, header_size) {
            let mut copy = [0u8; RUNTIME_FUNCTION_SIZE];
            copy.copy_from_slice(entry);
            valid.push(copy);
        } else {
            invalid = invalid.saturating_add(1);
        }
    }
    Ok(ExceptionScan { valid, invalid })
}

fn runtime_function_ranges(valid: &[[u8; RUNTIME_FUNCTION_SIZE]]) -> UnwindRanges {
    valid
        .iter()
        .filter_map(|entry| Some((read_u32(entry, 0).ok()?, read_u32(entry, 4).ok()?)))
        .collect()
}

fn write_valid_runtime_functions(
    output: &mut [u8],
    entry_offset: usize,
    file_offset: usize,
    size: usize,
    valid: &[[u8; RUNTIME_FUNCTION_SIZE]],
) -> AppResult<()> {
    let range_end = file_offset
        .checked_add(size)
        .ok_or_else(|| AppError::new("exception-directory range overflowed"))?;
    let destination = output
        .get_mut(file_offset..range_end)
        .ok_or_else(|| AppError::new("exception directory lies outside the rebuilt PE"))?;
    destination.fill(0);
    for (index, entry) in valid.iter().enumerate() {
        let start = index.saturating_mul(RUNTIME_FUNCTION_SIZE);
        let end = start.saturating_add(RUNTIME_FUNCTION_SIZE);
        if let Some(slot) = destination.get_mut(start..end) {
            slot.copy_from_slice(entry);
        }
    }
    if valid.is_empty() {
        write_u32(output, entry_offset, 0)?;
        write_u32(output, entry_offset.saturating_add(4), 0)?;
        return Ok(());
    }
    let new_size = valid
        .len()
        .checked_mul(RUNTIME_FUNCTION_SIZE)
        .and_then(|value| u32::try_from(value).ok())
        .ok_or_else(|| AppError::new("exception-directory size overflowed"))?;
    write_u32(output, entry_offset.saturating_add(4), new_size)
}

fn entry_unwind_covered(ranges: &Option<UnwindRanges>, entry: u32) -> Option<bool> {
    let ranges = ranges.as_ref()?;
    Some(
        ranges
            .iter()
            .any(|(begin, end)| entry >= *begin && entry < *end),
    )
}

fn count_write_execute_sections(
    layouts: &[SectionLayout<'_>],
    regions: &[RegionEvidence],
) -> usize {
    layouts
        .iter()
        .filter(|layout| {
            let start = layout.model.virtual_address.get() as usize;
            let end = start.saturating_add(layout.source_length);
            regions.iter().any(|region| {
                region.writable
                    && region.executable
                    && region.offset < end
                    && start < region.offset.saturating_add(region.size)
            })
        })
        .count()
}

fn absent_sections(memory: &[u8], layouts: &[SectionLayout<'_>]) -> usize {
    layouts
        .iter()
        .filter(|layout| section_absent(memory, layout))
        .count()
}

fn section_absent(memory: &[u8], layout: &SectionLayout<'_>) -> bool {
    if layout.model.characteristics & IMAGE_SCN_MEM_EXECUTE == 0 {
        return false;
    }
    if layout.source_length < MIN_ABSENT_SECTION_BYTES {
        return false;
    }
    let start = layout.model.virtual_address.get() as usize;
    let Some(slice) = memory.get(start..start.saturating_add(layout.source_length)) else {
        return false;
    };
    slice.iter().all(|byte| *byte == 0)
}

fn never_decrypted_sections(
    memory: &[u8],
    layouts: &[SectionLayout<'_>],
    page_flags: &[u8],
) -> usize {
    layouts
        .iter()
        .filter(|layout| section_never_decrypted(memory, layout, page_flags))
        .count()
}

fn section_never_decrypted(memory: &[u8], layout: &SectionLayout<'_>, page_flags: &[u8]) -> bool {
    if layout.model.characteristics & IMAGE_SCN_MEM_EXECUTE == 0 {
        return false;
    }
    let start = layout.model.virtual_address.get() as usize;
    let Some(slice) = memory.get(start..start.saturating_add(layout.source_length)) else {
        return false;
    };
    let trimmed = trim_trailing_zeroes(slice);
    if trimmed.len() < MIN_ENTROPY_SECTION_BYTES {
        return false;
    }
    let first_page = start / PAGE_SIZE;
    let page_count = layout.source_length.div_ceil(PAGE_SIZE);
    let Some(pages) = page_flags.get(first_page..first_page.saturating_add(page_count)) else {
        return false;
    };
    if !pages.iter().any(|flags| flags & PAGE_RESIDENT != 0) {
        return false;
    }
    if pages.iter().any(|flags| flags & PAGE_PRIVATE != 0) {
        return false;
    }
    shannon_entropy(trimmed) >= HIGH_ENTROPY_THRESHOLD
}

fn trim_trailing_zeroes(bytes: &[u8]) -> &[u8] {
    let Some(last) = bytes.iter().rposition(|byte| *byte != 0) else {
        return &[];
    };
    bytes.get(..=last).unwrap_or(bytes)
}

fn shannon_entropy(bytes: &[u8]) -> f64 {
    if bytes.is_empty() {
        return 0.0;
    }
    let mut counts = [0u32; ENTROPY_ALPHABET];
    for byte in bytes {
        if let Some(count) = counts.get_mut(usize::from(*byte)) {
            *count = count.saturating_add(1);
        }
    }
    let total = bytes.len() as f64;
    let mut entropy = 0.0f64;
    for count in counts {
        if count == 0 {
            continue;
        }
        let share = f64::from(count) / total;
        entropy -= share * share.log2();
    }
    entropy
}

fn runtime_function_is_valid(
    output: &[u8],
    entry: &[u8],
    model: &PeModel,
    layouts: &[SectionLayout<'_>],
    header_size: usize,
) -> bool {
    let Ok(begin) = read_u32(entry, 0) else {
        return false;
    };
    let Ok(end) = read_u32(entry, 4) else {
        return false;
    };
    let Ok(unwind) = read_u32(entry, 8) else {
        return false;
    };
    if begin >= end
        || !model.executable_rva(Rva(begin))
        || !model.executable_rva(Rva(end.saturating_sub(1)))
    {
        return false;
    }
    let Some(unwind_offset) = rva_to_file(unwind, layouts, header_size) else {
        return false;
    };
    let Some(first) = output.get(unwind_offset).copied() else {
        return false;
    };
    matches!(first & 0x07, 1 | 2)
}

fn repair_debug_directory(
    output: &mut [u8],
    model: &PeModel,
    layouts: &[SectionLayout<'_>],
    header_size: usize,
) -> AppResult<usize> {
    if DEBUG_DIRECTORY >= model.directory_count {
        return Ok(0);
    }
    let entry_offset = model
        .directory_offset(DEBUG_DIRECTORY)?
        .ok_or_else(|| AppError::new("debug-directory slot is missing"))?;
    let rva = read_u32(output, entry_offset)?;
    let size = read_u32(output, entry_offset.saturating_add(4))? as usize;
    if rva == 0 || size < DEBUG_ENTRY_SIZE {
        return Ok(0);
    }
    let Some(table_offset) = rva_to_file(rva, layouts, header_size) else {
        return Ok(0);
    };
    let count = (size / DEBUG_ENTRY_SIZE).min(MAX_DEBUG_ENTRIES);
    let mut repaired = 0usize;
    for index in 0..count {
        let entry = table_offset
            .checked_add(index.saturating_mul(DEBUG_ENTRY_SIZE))
            .ok_or_else(|| AppError::new("debug-directory entry offset overflowed"))?;
        let pointer_offset = entry.saturating_add(DEBUG_ENTRY_RAW_POINTER);
        let (Ok(raw_rva), Ok(stored)) = (
            read_u32(output, entry.saturating_add(DEBUG_ENTRY_RAW_RVA)),
            read_u32(output, pointer_offset),
        ) else {
            break;
        };
        let pointer = (raw_rva != 0)
            .then(|| rva_to_file(raw_rva, layouts, header_size))
            .flatten()
            .and_then(|offset| u32::try_from(offset).ok())
            .unwrap_or(0);
        if stored != pointer {
            write_u32(output, pointer_offset, pointer)?;
            repaired = repaired.saturating_add(1);
        }
    }
    Ok(repaired)
}

fn clear_dynamic_base(output: &mut [u8], model: &PeModel) -> AppResult<bool> {
    if let Some(offset) = model.directory_offset(BASERELOC_DIRECTORY)?
        && read_u32(output, offset)? != 0
        && read_u32(output, offset.saturating_add(4))? != 0
    {
        return Ok(false);
    }
    let characteristics = read_u16(output, model.dll_characteristics_offset)?;
    if characteristics & IMAGE_DLLCHARACTERISTICS_DYNAMIC_BASE == 0 {
        return Ok(false);
    }
    write_u16(
        output,
        model.dll_characteristics_offset,
        characteristics & !IMAGE_DLLCHARACTERISTICS_DYNAMIC_BASE,
    )?;
    Ok(true)
}

fn append_import_section(
    output: &mut Vec<u8>,
    model: &PeModel,
    plan: &ImportPlan,
) -> AppResult<(bool, bool)> {
    if IMPORT_DIRECTORY >= model.directory_count {
        return Ok((false, false));
    }
    let section_header = model
        .sections
        .iter()
        .map(|section| section.header_offset)
        .max()
        .and_then(|offset| offset.checked_add(SECTION_HEADER_SIZE))
        .ok_or_else(|| AppError::new("new section-header offset overflowed"))?;
    let header_limit = usize::try_from(read_u32(output, model.size_of_headers_offset)?)
        .map_err(|_| AppError::new("PE header size does not fit memory"))?;
    if section_header.saturating_add(SECTION_HEADER_SIZE) > header_limit {
        return Ok((false, false));
    }
    let virtual_address = align_up_u64(
        u64::from(read_u32(output, model.size_of_image_offset)?),
        u64::from(model.section_alignment),
    )?;
    let virtual_address = u32::try_from(virtual_address)
        .map_err(|_| AppError::new("import section RVA exceeds u32"))?;
    let payload = build_import_payload(plan, model.kind, virtual_address)?;
    let raw_offset = align_up(output.len(), model.file_alignment as usize)?;
    let raw_size = align_up(payload.len(), model.file_alignment as usize)?;
    let final_size = raw_offset
        .checked_add(raw_size)
        .ok_or_else(|| AppError::new("import section output size overflowed"))?;
    if final_size > MAX_OUTPUT_SIZE {
        return Err(AppError::new(
            "recovered imports exceed the 1 GiB output safety limit",
        ));
    }
    output.resize(final_size, 0);
    let payload_end = raw_offset
        .checked_add(payload.len())
        .ok_or_else(|| AppError::new("import payload range overflowed"))?;
    output
        .get_mut(raw_offset..payload_end)
        .ok_or_else(|| AppError::new("import payload lies outside the rebuilt PE"))?
        .copy_from_slice(&payload);

    write_mempe_section_header(
        output,
        section_header,
        virtual_address,
        payload.len(),
        raw_offset,
        raw_size,
    )?;
    let iat_cleared = commit_import_section(output, model, plan, virtual_address, payload.len())?;
    Ok((true, iat_cleared))
}

fn write_mempe_section_header(
    output: &mut [u8],
    section_header: usize,
    virtual_address: u32,
    virtual_size: usize,
    raw_offset: usize,
    raw_size: usize,
) -> AppResult<()> {
    let name = output
        .get_mut(section_header..section_header.saturating_add(8))
        .ok_or_else(|| AppError::new("new section name lies outside the PE headers"))?;
    name.copy_from_slice(b".mempe\0\0");
    write_u32(
        output,
        section_header.saturating_add(8),
        u32::try_from(virtual_size)
            .map_err(|_| AppError::new("import payload size exceeds u32"))?,
    )?;
    write_u32(output, section_header.saturating_add(12), virtual_address)?;
    write_u32(
        output,
        section_header.saturating_add(16),
        u32::try_from(raw_size).map_err(|_| AppError::new("import raw size exceeds u32"))?,
    )?;
    write_u32(
        output,
        section_header.saturating_add(20),
        u32::try_from(raw_offset).map_err(|_| AppError::new("import file offset exceeds u32"))?,
    )?;
    write_u32(
        output,
        section_header.saturating_add(36),
        MEMPE_IMPORT_CHARACTERISTICS,
    )
}

fn commit_import_section(
    output: &mut [u8],
    model: &PeModel,
    plan: &ImportPlan,
    virtual_address: u32,
    payload_len: usize,
) -> AppResult<bool> {
    let section_count_offset = model.nt_offset.saturating_add(6);
    let section_count = read_u16(output, section_count_offset)?
        .checked_add(1)
        .ok_or_else(|| AppError::new("section count overflowed"))?;
    write_u16(output, section_count_offset, section_count)?;
    let image_end = u64::from(virtual_address)
        .checked_add(payload_len as u64)
        .ok_or_else(|| AppError::new("import virtual range overflowed"))?;
    let image_size = align_up_u64(image_end, u64::from(model.section_alignment))?;
    write_u32(
        output,
        model.size_of_image_offset,
        u32::try_from(image_size).map_err(|_| AppError::new("image size exceeds u32"))?,
    )?;
    let descriptor_size = u32::try_from(import_descriptor_bytes(plan)?)
        .map_err(|_| AppError::new("import descriptor size exceeds u32"))?;
    write_directory(
        output,
        model,
        IMPORT_DIRECTORY,
        virtual_address,
        descriptor_size,
    )?;
    if plan.existing.is_empty() {
        return Ok(clear_directory(output, model, IAT_DIRECTORY)? > 0);
    }
    Ok(false)
}

fn build_import_payload(plan: &ImportPlan, kind: PeKind, section_rva: u32) -> AppResult<Vec<u8>> {
    let width = kind.pointer_width();
    let mut payload = plan.existing.clone();
    payload.resize(import_descriptor_bytes(plan)?, 0);
    for (group_index, group) in plan.groups.iter().enumerate() {
        align_vec(&mut payload, width);
        let lookup_offset = payload.len();
        let lookup_size = group
            .entries
            .len()
            .checked_add(1)
            .and_then(|count| count.checked_mul(width))
            .ok_or_else(|| AppError::new("import lookup-table size overflowed"))?;
        payload.resize(payload.len().saturating_add(lookup_size), 0);
        write_lookup_thunks(&mut payload, group, kind, section_rva, lookup_offset)?;
        let module_offset = payload.len();
        append_ascii(&mut payload, &group.module)?;
        let descriptor = group_index
            .checked_mul(IMPORT_DESCRIPTOR_SIZE)
            .and_then(|offset| offset.checked_add(plan.existing.len()))
            .ok_or_else(|| AppError::new("import descriptor offset overflowed"))?;
        write_import_descriptor(
            &mut payload,
            descriptor,
            section_rva,
            lookup_offset,
            module_offset,
            group.first_thunk,
        )?;
    }
    Ok(payload)
}

fn write_lookup_thunks(
    payload: &mut Vec<u8>,
    group: &ImportGroup,
    kind: PeKind,
    section_rva: u32,
    lookup_offset: usize,
) -> AppResult<()> {
    let width = kind.pointer_width();
    for (entry_index, entry) in group.entries.iter().enumerate() {
        let thunk = match &entry.name {
            Some(name) => {
                align_vec(payload, 2);
                let name_offset = payload.len();
                payload.extend_from_slice(&[0, 0]);
                append_ascii(payload, name)?;
                u64::from(section_rva)
                    .checked_add(name_offset as u64)
                    .ok_or_else(|| AppError::new("import name RVA overflowed"))?
            }
            None => ordinal_thunk(kind, entry.ordinal),
        };
        let thunk_offset = lookup_offset
            .checked_add(entry_index.saturating_mul(width))
            .ok_or_else(|| AppError::new("import thunk offset overflowed"))?;
        write_thunk(payload, thunk_offset, kind, thunk)?;
    }
    Ok(())
}

fn ordinal_thunk(kind: PeKind, ordinal: u32) -> u64 {
    let flag = if kind == PeKind::Pe32 {
        0x8000_0000u64
    } else {
        0x8000_0000_0000_0000u64
    };
    flag | u64::from(ordinal & 0xffff)
}

fn write_import_descriptor(
    payload: &mut [u8],
    descriptor: usize,
    section_rva: u32,
    lookup_offset: usize,
    module_offset: usize,
    first_thunk: u32,
) -> AppResult<()> {
    write_u32(
        payload,
        descriptor,
        payload_rva(section_rva, lookup_offset, "import lookup-table")?,
    )?;
    write_u32(
        payload,
        descriptor.saturating_add(12),
        payload_rva(section_rva, module_offset, "import module")?,
    )?;
    write_u32(payload, descriptor.saturating_add(16), first_thunk)
}

fn payload_rva(section_rva: u32, offset: usize, what: &str) -> AppResult<u32> {
    let offset =
        u32::try_from(offset).map_err(|_| AppError::new(format!("{what} offset exceeds u32")))?;
    section_rva
        .checked_add(offset)
        .ok_or_else(|| AppError::new(format!("{what} RVA overflowed")))
}

fn readable_section_name(name: &[u8; 8], position: usize) -> Option<[u8; 8]> {
    let end = name
        .iter()
        .position(|byte| *byte == 0)
        .unwrap_or(name.len());
    let label = name.get(..end)?;
    let readable = label
        .iter()
        .all(|byte| (PRINTABLE_FIRST..=PRINTABLE_LAST).contains(byte))
        && label.iter().any(|byte| *byte != b' ');
    if readable {
        return None;
    }
    let text = format!(".sec{position:02}");
    let bytes = text.as_bytes();
    let mut replacement = [0u8; SECTION_NAME_SIZE];
    replacement.get_mut(..bytes.len())?.copy_from_slice(bytes);
    Some(replacement)
}

fn count_tls_callbacks(image: &PeImage<'_>, observed_base: usize) -> usize {
    let Ok(Some(directory)) = image.directory(TLS_DIRECTORY) else {
        return 0;
    };
    let model = image.model();
    let memory = image.bytes();
    let width: usize = if model.kind() == PeKind::Pe32 { 4 } else { 8 };
    let Some(table_offset) = width
        .checked_mul(3)
        .and_then(|offset| directory.rva().as_usize().checked_add(offset))
    else {
        return 0;
    };
    let Ok(table) = read_pointer(memory, table_offset, model.kind()) else {
        return 0;
    };
    let Some(table_rva) = table.checked_sub(observed_base) else {
        return 0;
    };
    let mut count = 0usize;
    for index in 0..MAX_TLS_CALLBACKS {
        let Some(offset) = index
            .checked_mul(width)
            .and_then(|offset| table_rva.checked_add(offset))
        else {
            break;
        };
        match read_pointer(memory, offset, model.kind()) {
            Ok(0) | Err(_) => break,
            Ok(_) => count = count.saturating_add(1),
        }
    }
    count
}

fn entry_section_name(layouts: &[SectionLayout<'_>], entry_point: u32) -> Option<String> {
    let rva = Rva(entry_point);
    let (index, layout) = layouts
        .iter()
        .enumerate()
        .find(|(_, layout)| layout.model.contains_rva(rva))?;
    let name = readable_section_name(layout.model.name(), index.saturating_add(1))
        .unwrap_or(*layout.model.name());
    let end = name
        .iter()
        .position(|byte| *byte == 0)
        .unwrap_or(name.len());
    let label = String::from_utf8_lossy(name.get(..end)?).into_owned();
    (!label.is_empty()).then_some(label)
}

fn import_descriptor_bytes(plan: &ImportPlan) -> AppResult<usize> {
    plan.groups
        .len()
        .checked_add(1)
        .and_then(|count| count.checked_mul(IMPORT_DESCRIPTOR_SIZE))
        .and_then(|size| size.checked_add(plan.existing.len()))
        .ok_or_else(|| AppError::new("import descriptor size overflowed"))
}

fn append_ascii(bytes: &mut Vec<u8>, value: &str) -> AppResult<()> {
    if value.is_empty() || !value.is_ascii() || value.as_bytes().contains(&0) {
        return Err(AppError::new("import name is not valid ASCII"));
    }
    bytes.extend_from_slice(value.as_bytes());
    bytes.push(0);
    Ok(())
}

fn align_vec(bytes: &mut Vec<u8>, alignment: usize) {
    bytes.resize(bytes.len().next_multiple_of(alignment), 0);
}

fn write_thunk(bytes: &mut [u8], offset: usize, kind: PeKind, value: u64) -> AppResult<()> {
    match kind {
        PeKind::Pe32 => write_u32(
            bytes,
            offset,
            u32::try_from(value).map_err(|_| AppError::new("PE32 import thunk exceeds u32"))?,
        ),
        PeKind::Pe32Plus => write_u64(bytes, offset, value),
    }
}

fn write_directory(
    output: &mut [u8],
    model: &PeModel,
    index: usize,
    rva: u32,
    size: u32,
) -> AppResult<()> {
    let offset = model
        .directory_offset(index)?
        .ok_or_else(|| AppError::new("PE has no requested data-directory slot"))?;
    write_u32(output, offset, rva)?;
    write_u32(output, offset.saturating_add(4), size)
}

fn clear_directory(output: &mut [u8], model: &PeModel, index: usize) -> AppResult<usize> {
    let Some(offset) = model.directory_offset(index)? else {
        return Ok(0);
    };
    let was_set =
        read_u32(output, offset)? != 0 || read_u32(output, offset.saturating_add(4))? != 0;
    write_u32(output, offset, 0)?;
    write_u32(output, offset.saturating_add(4), 0)?;
    Ok(usize::from(was_set))
}

fn rva_to_file(rva: u32, layouts: &[SectionLayout<'_>], header_size: usize) -> Option<usize> {
    let rva = rva as usize;
    if rva < header_size {
        return Some(rva);
    }
    layouts.iter().find_map(|layout| {
        let start = layout.model.virtual_address.get() as usize;
        let delta = rva.checked_sub(start)?;
        (delta < layout.source_length).then(|| layout.raw_offset.saturating_add(delta))
    })
}

fn directory_is_mapped(
    rva: u32,
    size: u32,
    layouts: &[SectionLayout<'_>],
    header_size: usize,
) -> bool {
    if size == 0 {
        return false;
    }
    let start = rva as usize;
    let Some(end) = start.checked_add(size as usize) else {
        return false;
    };
    if end <= header_size {
        return true;
    }
    layouts.iter().any(|layout| {
        let section_start = layout.model.virtual_address.get() as usize;
        let section_end = section_start.saturating_add(layout.source_length);
        start >= section_start && end <= section_end
    })
}

fn align_up(value: usize, alignment: usize) -> AppResult<usize> {
    if alignment == 0 || !alignment.is_power_of_two() {
        return Err(AppError::new("PE alignment is invalid"));
    }
    value
        .checked_add(alignment - 1)
        .map(|result| result & !(alignment - 1))
        .ok_or_else(|| AppError::new("PE alignment overflowed"))
}

fn align_up_u64(value: u64, alignment: u64) -> AppResult<u64> {
    if alignment == 0 || !alignment.is_power_of_two() {
        return Err(AppError::new("PE alignment is invalid"));
    }
    value
        .checked_add(alignment - 1)
        .map(|result| result & !(alignment - 1))
        .ok_or_else(|| AppError::new("PE alignment overflowed"))
}

#[cfg(test)]
mod tests {
    use pelite::PeFile;

    use super::{
        IMAGE_SCN_CNT_CODE, IMAGE_SCN_CNT_INITIALIZED_DATA, IMAGE_SCN_MEM_EXECUTE,
        IMAGE_SCN_MEM_READ, IMAGE_SCN_MEM_WRITE, compute_checksum, directory_name,
        entry_unwind_covered, is_notable_directory, readable_section_name, rebuild,
        recovered_characteristics, shannon_entropy,
    };
    use crate::pe::{EntryPointRva, ExportIndex, PeKind, RegionEvidence};

    #[test]
    fn rebuilds_a_memory_layout_pe32_plus() -> Result<(), Box<dyn std::error::Error>> {
        let memory = fixture_pe64();
        let rebuilt = rebuild(
            &memory,
            &[],
            0x0000_7FF6_0000_0000,
            None,
            &ExportIndex::default(),
            None,
            &[],
        )?;

        assert!(!rebuilt.is_dll);
        assert_eq!(rebuilt.section_count, 1);
        assert!(PeFile::from_bytes(&rebuilt.bytes).is_ok());
        assert_eq!(&rebuilt.bytes[0x200..0x204], &[0x90, 0x90, 0xC3, 0]);
        Ok(())
    }

    #[test]
    fn rebuilds_a_memory_layout_pe32_dll() -> Result<(), Box<dyn std::error::Error>> {
        let memory = fixture_pe32();
        let rebuilt = rebuild(
            &memory,
            &[],
            0x0040_0000,
            None,
            &ExportIndex::default(),
            None,
            &[],
        )?;

        assert!(rebuilt.is_dll);
        assert_eq!(rebuilt.kind, PeKind::Pe32);
        assert!(PeFile::from_bytes(&rebuilt.bytes).is_ok());
        assert_eq!(&rebuilt.bytes[0x200..0x204], &[0x55, 0x8B, 0xEC, 0xC3]);
        Ok(())
    }

    #[test]
    fn restores_damaged_headers_from_disk_structure() -> Result<(), Box<dyn std::error::Error>> {
        let mut disk = fixture_pe64();
        put_u32(&mut disk, 0x98 + 60, 0x000F_0000);
        let mut memory = disk.clone();
        memory[..0x200].fill(0);

        let rebuilt = rebuild(
            &memory,
            &[],
            0x0000_7FF6_0000_0000,
            Some(&disk),
            &ExportIndex::default(),
            None,
            &[],
        )?;

        assert!(rebuilt.disk_headers_used);
        assert!(PeFile::from_bytes(&rebuilt.bytes).is_ok());
        assert_eq!(&rebuilt.bytes[0x200..0x204], &[0x90, 0x90, 0xC3, 0]);
        Ok(())
    }

    #[test]
    fn preserves_valid_memory_entry_point_during_disk_merge()
    -> Result<(), Box<dyn std::error::Error>> {
        let disk = fixture_pe64();
        let mut memory = disk.clone();
        put_u32(&mut memory, 0x80, 0);
        put_u32(&mut memory, 0x98 + 16, 0x1001);

        let rebuilt = rebuild(
            &memory,
            &[],
            0x0000_7FF6_0000_0000,
            Some(&disk),
            &ExportIndex::default(),
            None,
            &[],
        )?;

        assert!(rebuilt.disk_headers_used);
        assert_eq!(get_u32(&rebuilt.bytes, 0x98 + 16), 0x1001);
        Ok(())
    }

    #[test]
    fn rejects_disk_headers_that_conflict_with_memory_architecture() {
        let disk = fixture_pe64();
        let mut memory = disk.clone();
        put_u32(&mut memory, 0x80, 0);
        put_u16(&mut memory, 0x84, 0x014C);

        let result = rebuild(
            &memory,
            &[],
            0x0000_7FF6_0000_0000,
            Some(&disk),
            &ExportIndex::default(),
            None,
            &[],
        );

        assert!(result.is_err());
    }

    #[test]
    fn applies_only_valid_manual_entry_points() -> Result<(), Box<dyn std::error::Error>> {
        let memory = fixture_pe64();
        let valid = EntryPointRva::new(0x1002).ok_or("valid entry point is missing")?;
        let invalid = EntryPointRva::new(0x180).ok_or("invalid test entry point is missing")?;

        let rebuilt = rebuild(
            &memory,
            &[],
            0x0000_7FF6_0000_0000,
            None,
            &ExportIndex::default(),
            Some(valid),
            &[],
        )?;
        let invalid_result = rebuild(
            &memory,
            &[],
            0x0000_7FF6_0000_0000,
            None,
            &ExportIndex::default(),
            Some(invalid),
            &[],
        );

        assert_eq!(get_u32(&rebuilt.bytes, 0x98 + 16), 0x1002);
        assert!(invalid_result.is_err());
        Ok(())
    }

    #[test]
    fn recalculates_derived_optional_header_fields() -> Result<(), Box<dyn std::error::Error>> {
        let mut memory = fixture_pe64();
        let section = 0x98 + 0xF0;
        put_u32(&mut memory, 0x98 + 4, 1);
        put_u32(&mut memory, 0x98 + 8, 2);
        put_u32(&mut memory, 0x98 + 12, 3);
        put_u32(&mut memory, 0x98 + 20, 4);
        put_u32(&mut memory, section + 36, 0xE000_00E0);

        let rebuilt = rebuild(
            &memory,
            &[],
            0x0000_7FF6_0000_0000,
            None,
            &ExportIndex::default(),
            None,
            &[],
        )?;

        assert_eq!(get_u32(&rebuilt.bytes, 0x98 + 4), 0x1000);
        assert_eq!(get_u32(&rebuilt.bytes, 0x98 + 8), 0x1000);
        assert_eq!(get_u32(&rebuilt.bytes, 0x98 + 12), 0x1000);
        assert_eq!(get_u32(&rebuilt.bytes, 0x98 + 20), 0x1000);
        Ok(())
    }

    #[test]
    fn removes_invalid_x64_unwind_entries() -> Result<(), Box<dyn std::error::Error>> {
        let mut memory = fixture_pe64();
        let optional = 0x98;
        put_u32(&mut memory, optional + 112 + 3 * 8, 0x1100);
        put_u32(&mut memory, optional + 112 + 3 * 8 + 4, 12);
        put_u32(&mut memory, 0x1100, 0x1000);
        put_u32(&mut memory, 0x1104, 0x1010);
        put_u32(&mut memory, 0x1108, 0x1200);

        let rebuilt = rebuild(
            &memory,
            &[],
            0x0000_7FF6_0000_0000,
            None,
            &ExportIndex::default(),
            None,
            &[],
        )?;

        assert_eq!(rebuilt.invalid_unwind_entries, 1);
        assert!(PeFile::from_bytes(&rebuilt.bytes).is_ok());
        Ok(())
    }

    #[test]
    fn recovers_section_access_from_committed_memory() -> Result<(), Box<dyn std::error::Error>> {
        let mut memory = fixture_pe64();
        let section = 0x98 + 0xF0;
        put_u32(&mut memory, section + 36, IMAGE_SCN_CNT_INITIALIZED_DATA);
        let regions = [RegionEvidence {
            offset: 0x1000,
            size: 0x1000,
            readable: true,
            writable: false,
            executable: true,
        }];

        let rebuilt = rebuild(
            &memory,
            &regions,
            0x0000_7FF6_0000_0000,
            None,
            &ExportIndex::default(),
            None,
            &[],
        )?;
        let characteristics = get_u32(&rebuilt.bytes, section + 36);

        assert_ne!(characteristics & IMAGE_SCN_MEM_EXECUTE, 0);
        assert_ne!(characteristics & IMAGE_SCN_MEM_READ, 0);
        assert_ne!(characteristics & IMAGE_SCN_CNT_CODE, 0);
        assert_eq!(characteristics & IMAGE_SCN_MEM_WRITE, 0);
        Ok(())
    }

    #[test]
    fn repoints_debug_entries_at_the_rebuilt_layout() -> Result<(), Box<dyn std::error::Error>> {
        let mut memory = fixture_pe64();
        let optional = 0x98;
        put_u32(&mut memory, optional + 112 + 6 * 8, 0x1100);
        put_u32(&mut memory, optional + 112 + 6 * 8 + 4, 28);
        put_u32(&mut memory, 0x1100 + 20, 0x1200);
        put_u32(&mut memory, 0x1100 + 24, 0xDEAD);

        let rebuilt = rebuild(
            &memory,
            &[],
            0x0000_7FF6_0000_0000,
            None,
            &ExportIndex::default(),
            None,
            &[],
        )?;

        assert_eq!(rebuilt.repaired_debug_entries, 1);
        assert_eq!(get_u32(&rebuilt.bytes, 0x300 + 24), 0x400);
        assert_ne!(get_u32(&rebuilt.bytes, 0x98 + 112 + 6 * 8), 0);
        Ok(())
    }

    #[test]
    fn replaces_only_unreadable_section_names() {
        let printable = readable_section_name(b".text\0\0\0", 1);
        let empty = readable_section_name(b"\0\0\0\0\0\0\0\0", 3);
        let binary = readable_section_name(&[0xE7, 0x91, 0x2A, 0, 0, 0, 0, 0], 7);
        let blank = readable_section_name(b"        ", 2);

        assert_eq!(printable, None);
        assert_eq!(empty, Some(*b".sec03\0\0"));
        assert_eq!(binary, Some(*b".sec07\0\0"));
        assert_eq!(blank, Some(*b".sec02\0\0"));
    }

    #[test]
    fn requires_substantial_write_coverage() {
        let mut regions = [
            RegionEvidence {
                offset: 0x1000,
                size: 0x1000,
                readable: true,
                writable: true,
                executable: false,
            },
            RegionEvidence {
                offset: 0x2000,
                size: 0x3000,
                readable: true,
                writable: false,
                executable: false,
            },
        ];

        let sparse = recovered_characteristics(0, &regions, 0x1000, 0x5000);
        let retained = recovered_characteristics(IMAGE_SCN_MEM_WRITE, &regions, 0x1000, 0x5000);
        regions[0].size = 0x2000;
        regions[1].offset = 0x3000;
        regions[1].size = 0x2000;
        let substantial = recovered_characteristics(0, &regions, 0x1000, 0x5000);

        assert_eq!(sparse & IMAGE_SCN_MEM_WRITE, 0);
        assert_ne!(retained & IMAGE_SCN_MEM_WRITE, 0);
        assert_ne!(substantial & IMAGE_SCN_MEM_WRITE, 0);
    }

    #[test]
    fn recovers_runtime_data_beyond_declared_image_size() -> Result<(), Box<dyn std::error::Error>>
    {
        let mut memory = fixture_pe64();
        memory.resize(0x3000, 0);
        memory[0x2500] = 0xC3;
        let regions = [RegionEvidence {
            offset: 0x1000,
            size: 0x2000,
            readable: true,
            writable: false,
            executable: true,
        }];

        let rebuilt = rebuild(
            &memory,
            &regions,
            0x0000_7FF6_0000_0000,
            None,
            &ExportIndex::default(),
            None,
            &[],
        )?;
        let section = 0x98 + 0xF0;

        assert_eq!(get_u32(&rebuilt.bytes, section + 8), 0x1501);
        assert_eq!(get_u32(&rebuilt.bytes, 0x98 + 56), 0x3000);
        assert_eq!(rebuilt.bytes[0x1700], 0xC3);
        Ok(())
    }

    fn fixture_pe64() -> Vec<u8> {
        let mut image = vec![0u8; 0x2000];
        put_u16(&mut image, 0, 0x5A4D);
        put_u32(&mut image, 0x3c, 0x80);
        put_u32(&mut image, 0x80, 0x0000_4550);
        put_u16(&mut image, 0x84, 0x8664);
        put_u16(&mut image, 0x86, 1);
        put_u16(&mut image, 0x94, 0xF0);
        put_u16(&mut image, 0x96, 0x22);
        let optional = 0x98;
        put_u16(&mut image, optional, 0x20B);
        put_u32(&mut image, optional + 16, 0x1000);
        put_u64(&mut image, optional + 24, 0x0001_4000_0000);
        put_u32(&mut image, optional + 32, 0x1000);
        put_u32(&mut image, optional + 36, 0x200);
        put_u32(&mut image, optional + 56, 0x2000);
        put_u32(&mut image, optional + 60, 0x200);
        put_u32(&mut image, optional + 108, 16);
        let section = optional + 0xF0;
        image[section..section + 5].copy_from_slice(b".text");
        put_u32(&mut image, section + 8, 0x1000);
        put_u32(&mut image, section + 12, 0x1000);
        put_u32(&mut image, section + 16, 0x200);
        put_u32(&mut image, section + 36, 0x6000_0020);
        image[0x1000..0x1004].copy_from_slice(&[0x90, 0x90, 0xC3, 0]);
        image
    }

    fn fixture_pe32() -> Vec<u8> {
        let mut image = vec![0u8; 0x2000];
        put_u16(&mut image, 0, 0x5A4D);
        put_u32(&mut image, 0x3c, 0x80);
        put_u32(&mut image, 0x80, 0x0000_4550);
        put_u16(&mut image, 0x84, 0x014C);
        put_u16(&mut image, 0x86, 1);
        put_u16(&mut image, 0x94, 0xE0);
        put_u16(&mut image, 0x96, 0x2102);
        let optional = 0x98;
        put_u16(&mut image, optional, 0x10B);
        put_u32(&mut image, optional + 16, 0x1000);
        put_u32(&mut image, optional + 28, 0x0040_0000);
        put_u32(&mut image, optional + 32, 0x1000);
        put_u32(&mut image, optional + 36, 0x200);
        put_u32(&mut image, optional + 56, 0x2000);
        put_u32(&mut image, optional + 60, 0x200);
        put_u32(&mut image, optional + 92, 16);
        let section = optional + 0xE0;
        image[section..section + 5].copy_from_slice(b".text");
        put_u32(&mut image, section + 8, 0x1000);
        put_u32(&mut image, section + 12, 0x1000);
        put_u32(&mut image, section + 16, 0x200);
        put_u32(&mut image, section + 36, 0x6000_0020);
        image[0x1000..0x1004].copy_from_slice(&[0x55, 0x8B, 0xEC, 0xC3]);
        image
    }

    fn put_u16(bytes: &mut [u8], offset: usize, value: u16) {
        bytes[offset..offset + 2].copy_from_slice(&value.to_le_bytes());
    }

    fn put_u32(bytes: &mut [u8], offset: usize, value: u32) {
        bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
    }

    fn put_u64(bytes: &mut [u8], offset: usize, value: u64) {
        bytes[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
    }

    fn get_u32(bytes: &[u8], offset: usize) -> u32 {
        u32::from_le_bytes([
            bytes[offset],
            bytes[offset + 1],
            bytes[offset + 2],
            bytes[offset + 3],
        ])
    }

    #[test]
    fn folds_the_checksum_like_the_loader_does() -> Result<(), Box<dyn std::error::Error>> {
        assert_eq!(compute_checksum(&[0x01, 0x00, 0x02, 0x00])?, 7);
        assert_eq!(compute_checksum(&[0xFF, 0xFF, 0x05])?, 8);
        assert_eq!(compute_checksum(&[0xFF, 0xFF, 0xFF, 0xFF])?, 0x0001_0003);
        assert_eq!(compute_checksum(&[])?, 0);
        Ok(())
    }

    #[test]
    fn checksum_ignores_whatever_sat_in_the_field_before() -> Result<(), Box<dyn std::error::Error>>
    {
        let mut image = fixture_pe64();
        let index = ExportIndex::build([]);
        let first = rebuild(&image, &[], 0x0000_7FF6_0000_0000, None, &index, None, &[])?;

        put_u32(&mut image, 0x98 + 64, 0xDEAD_BEEF);
        let second = rebuild(&image, &[], 0x0000_7FF6_0000_0000, None, &index, None, &[])?;

        assert_eq!(first.bytes, second.bytes);
        Ok(())
    }

    #[test]
    fn measures_entropy_against_known_distributions() {
        let uniform = [7u8; 4096];
        let halves: Vec<u8> = (0..4096).map(|index| u8::from(index % 2 == 0)).collect();
        let spread: Vec<u8> = (0..=255u8).collect();

        assert!(shannon_entropy(&[]) == 0.0);
        assert!(shannon_entropy(&uniform) == 0.0);
        assert!((shannon_entropy(&halves) - 1.0).abs() < 1e-9);
        assert!((shannon_entropy(&spread) - 8.0).abs() < 1e-9);
    }

    #[test]
    fn real_code_stays_below_the_high_entropy_threshold() {
        let ciphertext: Vec<u8> = (0..8192u32)
            .map(|index| (index.wrapping_mul(2_654_435_761) >> 13) as u8)
            .collect();

        assert!(shannon_entropy(&ciphertext) >= super::HIGH_ENTROPY_THRESHOLD);
        assert!(shannon_entropy(&[0u8; 8192]) < super::HIGH_ENTROPY_THRESHOLD);
    }

    #[test]
    fn reports_unwind_coverage_only_when_the_directory_survived() {
        let ranges = Some(vec![(0x1000u32, 0x1100u32), (0x2000, 0x2010)]);

        assert_eq!(entry_unwind_covered(&None, 0x1000), None);
        assert_eq!(entry_unwind_covered(&ranges, 0x1000), Some(true));
        assert_eq!(entry_unwind_covered(&ranges, 0x10FF), Some(true));
        assert_eq!(entry_unwind_covered(&ranges, 0x1100), Some(false));
        assert_eq!(entry_unwind_covered(&ranges, 0x0FFF), Some(false));
    }

    #[test]
    fn separates_routine_directories_from_notable_ones() {
        assert_eq!(directory_name(1), "Import");
        assert_eq!(directory_name(4), "Certificate");
        assert_eq!(directory_name(99), "Unknown");
        assert!(!is_notable_directory(4));
        assert!(!is_notable_directory(11));
        assert!(is_notable_directory(1));
        assert!(is_notable_directory(2));
    }
}
