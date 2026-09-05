use std::env;
use std::process::Command;

fn command_output(program: &str, arguments: &[&str]) -> Option<String> {
    let output = Command::new(program).args(arguments).output().ok()?;
    if !output.status.success() {
        return None;
    }
    let text = String::from_utf8(output.stdout).ok()?;
    Some(text.trim().replace('\n', "\\n"))
}

fn main() {
    for variable in [
        "RUSTC",
        "TARGET",
        "HOST",
        "PROFILE",
        "OPT_LEVEL",
        "DEBUG",
        "CARGO_FEATURE_SOLVER",
        "CARGO_FEATURE_JSON",
        "CARGO_FEATURE_TRACE",
        "SIGIL_Z3_IDENTITY",
    ] {
        println!("cargo:rerun-if-env-changed={variable}");
    }
    println!("cargo:rerun-if-changed=../../Cargo.lock");
    println!("cargo:rerun-if-changed=../../Cargo.toml");
    println!("cargo:rerun-if-changed=../sigil-abi/Cargo.toml");
    println!("cargo:rerun-if-changed=../sigil-abi/src");

    let rustc = env::var("RUSTC").unwrap_or_else(|_| "rustc".to_owned());
    let rustc_identity = command_output(&rustc, &["--version", "--verbose"])
        .expect("rustc --version --verbose must be available for compiler identity");
    println!("cargo:rustc-env=SIGIL_RUSTC_IDENTITY={rustc_identity}");

    let build_identity = [
        ("target", env::var("TARGET").unwrap_or_default()),
        ("host", env::var("HOST").unwrap_or_default()),
        ("profile", env::var("PROFILE").unwrap_or_default()),
        ("opt_level", env::var("OPT_LEVEL").unwrap_or_default()),
        ("debug", env::var("DEBUG").unwrap_or_default()),
    ]
    .into_iter()
    .map(|(name, value)| format!("{name}={value}"))
    .collect::<Vec<_>>()
    .join(";");
    println!("cargo:rustc-env=SIGIL_BUILD_IDENTITY={build_identity}");

    let features = ["solver", "json", "trace"]
        .into_iter()
        .filter(|feature| {
            env::var_os(format!("CARGO_FEATURE_{}", feature.to_uppercase())).is_some()
        })
        .collect::<Vec<_>>()
        .join(",");
    println!("cargo:rustc-env=SIGIL_COMPILER_FEATURES={features}");

    let z3_identity = if env::var_os("CARGO_FEATURE_SOLVER").is_some() {
        env::var("SIGIL_Z3_IDENTITY")
            .ok()
            .filter(|value| !value.trim().is_empty())
            .or_else(|| command_output("z3", &["--version"]))
            .or_else(|| command_output("pkg-config", &["--modversion", "z3"]))
            .expect(
                "solver builds require a native Z3 identity; install `z3`, provide pkg-config metadata, or set SIGIL_Z3_IDENTITY",
            )
    } else {
        "solver-off".to_owned()
    };
    println!("cargo:rustc-env=SIGIL_Z3_IDENTITY={z3_identity}");
}
