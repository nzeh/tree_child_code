extern crate tree_child;

use tree_child::app;

/// Main function
fn main() {
    if let Err(e) = real_main() {
        eprintln!("{}", e);
        std::process::exit(1);
    }
}

/// The real main function
fn real_main() -> app::Result<()> {
    let cfg    = app::Config::new();
    let trees  = app::read_input(&cfg.input)?;
    let tc_seq = app::tree_child_sequence(&cfg, trees);
    app::write_output(cfg.output.as_ref().map(|s| &s[..]), tc_seq)
}
