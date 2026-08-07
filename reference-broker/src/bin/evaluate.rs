use std::error::Error;
use std::path::PathBuf;

use proveai_reference_broker::evaluation::run_evaluation;

fn main() -> Result<(), Box<dyn Error>> {
    let mut iterations = 100u64;
    let mut output = None;
    let mut arguments = std::env::args().skip(1);
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--iterations" => {
                iterations = arguments
                    .next()
                    .ok_or("--iterations requires a value")?
                    .parse()?;
            }
            "--output" => {
                output = Some(PathBuf::from(
                    arguments.next().ok_or("--output requires a path")?,
                ));
            }
            "--help" | "-h" => {
                println!(
                    "Usage: cargo run --release --bin evaluate -- [--iterations N] [--output PATH]"
                );
                return Ok(());
            }
            _ => return Err(format!("unknown argument: {argument}").into()),
        }
    }

    let report = run_evaluation(iterations)?;
    let json = report.to_json_pretty();
    if let Some(path) = output {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(&path, json)?;
        println!(
            "RQ1: {}/{} cases passed; RQ2: {} requests per primary workload; report: {}",
            report.rq1.cases.iter().filter(|case| case.passed).count(),
            report.rq1.cases.len(),
            report.iterations,
            path.display()
        );
    } else {
        print!("{json}");
    }
    Ok(())
}
