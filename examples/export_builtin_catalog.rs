//! Export canonical provider-registered definitions for frontend packaging.
//! Run at generation time, never while authoring frontend expressions.
use egglog_experimental::PortableTypeInfo;
use prost::Message;
use std::io::Write;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let catalog = egglog_experimental::new_experimental_egraph()
        .type_info()
        .portable_builtin_catalog()
        .map_err(std::io::Error::other)?;
    let bytes = catalog.definitions.encode_to_vec();
    if let Some(path) = std::env::args_os().nth(1) {
        std::fs::write(path, bytes)?;
    } else {
        std::io::stdout().lock().write_all(&bytes)?;
    }
    eprintln!("Backend builtin catalog (not graph state).");
    eprintln!(
        "Undescribed primitives: {:?}",
        catalog.undescribed_primitives
    );
    eprintln!("Undescribed families: {:?}", catalog.undescribed_families);
    eprintln!(
        "Undescribed family operations: {:?}",
        catalog.undescribed_family_primitives
    );
    eprintln!("Undescribed sorts: {:?}", catalog.undescribed_sorts);
    Ok(())
}
