use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn write_setup(path: &Path, module: &str, imports: &[(&str, &Path)]) {
    let import_artifacts = imports
        .iter()
        .map(|(name, path)| (*name, [*path]))
        .collect::<std::collections::BTreeMap<_, _>>();
    let setup = serde_json::json!({
        "plugins": [],
        "package": "lambda-sigil",
        "options": {},
        "name": module,
        "isModule": false,
        "importArts": import_artifacts,
        "dynlibs": [],
    });
    fs::write(
        path,
        serde_json::to_vec(&setup).expect("module setup is JSON"),
    )
    .expect("failed to write Lean module setup");
}

/// The `import LambdaSigil.*` lines a Lean source actually carries. Non-project imports
/// (`Init.*`) resolve through the toolchain and are deliberately ignored.
fn project_imports(lean_root: &Path, module: &str) -> Vec<String> {
    let source = lean_root.join(format!("{}.lean", module.replace('.', "/")));
    let text = fs::read_to_string(&source)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", source.display()));
    let mut imports = text
        .lines()
        .filter_map(|line| line.trim_start().strip_prefix("import "))
        .map(str::trim)
        .filter(|target| target.starts_with("LambdaSigil."))
        .map(str::to_owned)
        .collect::<Vec<_>>();
    imports.sort_unstable();
    imports
}

/// Fail closed if the build table's declared edges drift from the source: a missing edge
/// would only surface as an unresolved import on a fresh checkout, a stale one would link an
/// artifact the module no longer imports.
fn assert_declared_imports_match_source(lean_root: &Path, module: &str, declared: &[&str]) {
    let actual = project_imports(lean_root, module);
    let mut declared = declared.iter().map(|d| (*d).to_owned()).collect::<Vec<_>>();
    declared.sort_unstable();
    assert_eq!(
        actual, declared,
        "native build table for {module} disagrees with its source imports; \
         update the dependency list in build.rs"
    );
}

fn checked_output(command: &mut Command, description: &str) -> String {
    let output = command
        .output()
        .unwrap_or_else(|error| panic!("failed to run {description}: {error}"));
    if !output.status.success() {
        panic!(
            "{description} failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    String::from_utf8(output.stdout)
        .unwrap_or_else(|error| panic!("{description} returned non-UTF-8 output: {error}"))
}

fn compile_lean_module(
    lean_root: &Path,
    out: &Path,
    module: &str,
    imports: &[(&str, &Path)],
) -> (PathBuf, PathBuf) {
    let stem = module
        .rsplit('.')
        .next()
        .expect("Lean module has a final component");
    let generated = out.join(format!("{stem}.c"));
    let object = out.join(format!("{stem}.olean"));
    let setup = out.join(format!("{stem}.setup.json"));
    let source = format!("{}.lean", module.replace('.', "/"));
    write_setup(&setup, module, imports);
    let status = Command::new("lake")
        .current_dir(lean_root)
        .args(["env", "lean", "-c"])
        .arg(&generated)
        .arg("-o")
        .arg(&object)
        .arg("--setup")
        .arg(&setup)
        .arg(&source)
        .status()
        .unwrap_or_else(|error| panic!("failed to compile {module} to C: {error}"));
    assert!(status.success(), "Lean module {module} compilation failed");
    (generated, object)
}

fn main() {
    let manifest = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let repository = manifest
        .parent()
        .and_then(Path::parent)
        .expect("bridge crate must live under <repository>/crates")
        .to_path_buf();
    let lean_root = repository.join("proofs/lean");
    let kernel = lean_root.join("LambdaSigil/CombinedKernel.lean");
    let semantic_kernel = lean_root.join("LambdaSigil/SemanticKernel.lean");
    let host_profile_kernel = lean_root.join("LambdaSigil/HostProfileKernel.lean");
    let occurrence_wire = lean_root.join("LambdaSigil/OccurrenceWire.lean");
    let toolchain = lean_root.join("lean-toolchain");
    let shim = manifest.join("native/bridge.c");
    let out = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR"));
    let generated_kernel = out.join("CombinedKernel.c");
    let generated_semantic = out.join("SemanticKernel.c");
    let generated_host_profile = out.join("HostProfileKernel.c");
    let generated_occurrence_wire = out.join("OccurrenceWire.c");
    let combined_setup = out.join("CombinedKernel.setup.json");
    let semantic_setup = out.join("SemanticKernel.setup.json");
    let host_profile_setup = out.join("HostProfileKernel.setup.json");
    let occurrence_wire_setup = out.join("OccurrenceWire.setup.json");
    let combined_olean = out.join("CombinedKernel.olean");
    let semantic_olean = out.join("SemanticKernel.olean");
    let host_profile_olean = out.join("HostProfileKernel.olean");
    let occurrence_wire_olean = out.join("OccurrenceWire.olean");
    let parity_setup = out.join("HostProfileParity.setup.json");
    let occurrence_parity_setup = out.join("OccurrenceWireParity.setup.json");

    // Every project import must refer to the artifact produced from this same
    // source build, not an arbitrary cached .lake copy. These kernels import
    // only Init and the explicitly listed project modules.
    write_setup(&combined_setup, "LambdaSigil.CombinedKernel", &[]);
    let combined_imports = [("LambdaSigil.CombinedKernel", combined_olean.as_path())];
    write_setup(
        &semantic_setup,
        "LambdaSigil.SemanticKernel",
        &combined_imports,
    );
    write_setup(
        &host_profile_setup,
        "LambdaSigil.HostProfileKernel",
        &combined_imports,
    );
    write_setup(
        &parity_setup,
        "LambdaSigil.HostProfileParity",
        &[
            ("LambdaSigil.CombinedKernel", combined_olean.as_path()),
            (
                "LambdaSigil.HostProfileKernel",
                host_profile_olean.as_path(),
            ),
        ],
    );
    println!(
        "cargo:rustc-env=SIGIL_HOST_PROFILE_PARITY_SETUP={}",
        parity_setup.display()
    );
    let occurrence_imports = [
        ("LambdaSigil.CombinedKernel", combined_olean.as_path()),
        (
            "LambdaSigil.HostProfileKernel",
            host_profile_olean.as_path(),
        ),
    ];
    write_setup(
        &occurrence_wire_setup,
        "LambdaSigil.OccurrenceWire",
        &occurrence_imports,
    );
    write_setup(
        &occurrence_parity_setup,
        "LambdaSigil.OccurrenceWireParity",
        &[
            occurrence_imports[0],
            occurrence_imports[1],
            (
                "LambdaSigil.OccurrenceWire",
                occurrence_wire_olean.as_path(),
            ),
        ],
    );
    println!(
        "cargo:rustc-env=SIGIL_CSIR_V9_PARITY_SETUP={}",
        occurrence_parity_setup.display()
    );

    println!("cargo:rerun-if-changed={}", kernel.display());
    println!("cargo:rerun-if-changed={}", semantic_kernel.display());
    println!("cargo:rerun-if-changed={}", host_profile_kernel.display());
    println!("cargo:rerun-if-changed={}", occurrence_wire.display());
    println!("cargo:rerun-if-changed={}", toolchain.display());
    println!("cargo:rerun-if-changed={}", shim.display());
    println!("cargo:rerun-if-env-changed=SIGIL_LEAN_TARGET_PREFIX");

    let pinned = fs::read_to_string(&toolchain)
        .expect("proofs/lean/lean-toolchain must be readable")
        .trim()
        .to_owned();
    let actual = checked_output(
        Command::new("lake")
            .current_dir(&lean_root)
            .args(["env", "lean", "--version"]),
        "pinned Lean version probe",
    );
    let expected_version = pinned
        .strip_prefix("leanprover/lean4:v")
        .unwrap_or(pinned.as_str());
    let expected_probe = format!("version {expected_version},");
    if !actual.contains(&expected_probe) {
        panic!("Lean toolchain drift: lean-toolchain pins `{pinned}`, probe returned `{actual}`");
    }

    let status = Command::new("lake")
        .current_dir(&lean_root)
        .args(["env", "lean", "-c"])
        .arg(&generated_kernel)
        .arg("-o")
        .arg(&combined_olean)
        .arg("--setup")
        .arg(&combined_setup)
        .arg("LambdaSigil/CombinedKernel.lean")
        .status()
        .expect("failed to compile the Lean CSIR kernel to C");
    assert!(status.success(), "Lean CSIR kernel compilation failed");
    let status = Command::new("lake")
        .current_dir(&lean_root)
        .args(["env", "lean", "-c"])
        .arg(&generated_semantic)
        .arg("-o")
        .arg(&semantic_olean)
        .arg("--setup")
        .arg(&semantic_setup)
        .arg("LambdaSigil/SemanticKernel.lean")
        .status()
        .expect("failed to compile the Lean raw semantic verifier to C");
    assert!(
        status.success(),
        "Lean raw semantic verifier compilation failed"
    );
    let status = Command::new("lake")
        .current_dir(&lean_root)
        .args(["env", "lean", "-c"])
        .arg(&generated_host_profile)
        .arg("-o")
        .arg(&host_profile_olean)
        .arg("--setup")
        .arg(&host_profile_setup)
        .arg("LambdaSigil/HostProfileKernel.lean")
        .status()
        .expect("failed to compile the Lean host profile decoder to C");
    assert!(
        status.success(),
        "Lean host profile decoder compilation failed"
    );
    let status = Command::new("lake")
        .current_dir(&lean_root)
        .args(["env", "lean", "-c"])
        .arg(&generated_occurrence_wire)
        .arg("-o")
        .arg(&occurrence_wire_olean)
        .arg("--setup")
        .arg(&occurrence_wire_setup)
        .arg("LambdaSigil/OccurrenceWire.lean")
        .status()
        .expect("failed to compile the Lean v9 declaration decoder to C");
    assert!(
        status.success(),
        "Lean v9 declaration decoder compilation failed"
    );

    // Compile every executable dependency of the production v9 occurrence kernel from this
    // source build. Do not import arbitrary `.lake` artifacts: the resulting native verdict and
    // checker fingerprint must describe the same immutable sources.
    let mut native_artifacts = std::collections::BTreeMap::<&str, PathBuf>::from([
        ("LambdaSigil.CombinedKernel", combined_olean.clone()),
        ("LambdaSigil.SemanticKernel", semantic_olean.clone()),
        ("LambdaSigil.HostProfileKernel", host_profile_olean.clone()),
        ("LambdaSigil.OccurrenceWire", occurrence_wire_olean.clone()),
    ]);
    let v9_modules: &[(&str, &[&str])] = &[
        (
            "LambdaSigil.OccurrenceRegions",
            &["LambdaSigil.SemanticKernel"],
        ),
        (
            "LambdaSigil.OccurrenceRegionConstruction",
            &["LambdaSigil.OccurrenceRegions"],
        ),
        (
            "LambdaSigil.OccurrenceTransfer",
            &["LambdaSigil.OccurrenceRegions"],
        ),
        (
            "LambdaSigil.OccurrenceTransferConstruction",
            &["LambdaSigil.OccurrenceTransfer"],
        ),
        (
            "LambdaSigil.DecodedOccurrence",
            &[
                "LambdaSigil.OccurrenceRegionConstruction",
                "LambdaSigil.OccurrenceTransferConstruction",
            ],
        ),
        (
            "LambdaSigil.AncestorIntervals",
            &["LambdaSigil.OccurrenceRegions"],
        ),
        (
            "LambdaSigil.IntervalEscapeChecks",
            &["LambdaSigil.AncestorIntervals"],
        ),
        (
            "LambdaSigil.PriorityOccurrence",
            &[
                "LambdaSigil.OccurrenceTransfer",
                "LambdaSigil.IntervalEscapeChecks",
            ],
        ),
        (
            "LambdaSigil.OccurrenceInvocation",
            &["LambdaSigil.DecodedOccurrence"],
        ),
        (
            "LambdaSigil.RankedDecodedOccurrence",
            &[
                "LambdaSigil.DecodedOccurrence",
                "LambdaSigil.PriorityOccurrence",
                "LambdaSigil.OccurrenceInvocation",
            ],
        ),
        (
            "LambdaSigil.V9BoundaryContracts",
            &["LambdaSigil.OccurrenceWire"],
        ),
        (
            "LambdaSigil.V9OccurrenceDataflow",
            &[
                "LambdaSigil.V9BoundaryContracts",
                "LambdaSigil.SemanticKernel",
            ],
        ),
        (
            "LambdaSigil.V9OccurrenceDataflowInvocation",
            &[
                "LambdaSigil.V9OccurrenceDataflow",
                "LambdaSigil.RankedDecodedOccurrence",
            ],
        ),
        (
            "LambdaSigil.OccurrenceActivation",
            &["LambdaSigil.SemanticKernel"],
        ),
        (
            "LambdaSigil.V9OccurrenceKernel",
            &[
                "LambdaSigil.V9OccurrenceDataflowInvocation",
                "LambdaSigil.OccurrenceActivation",
            ],
        ),
    ];
    // Lean resolves an imported artifact's OWN imports through the same setup, so a module's
    // setup must carry its whole transitive project closure. Listing only the direct edge
    // passed locally because a cached `.lake` build sat on `lake env`'s search path, and failed
    // on every fresh checkout with "unknown module prefix 'LambdaSigil'" -- exactly the cached
    // artifact the comment above forbids. The base kernels' direct edges are declared here so
    // the closure is computed from one table, and every declared edge set is checked against
    // the source's actual `import LambdaSigil.*` lines so the table cannot drift.
    let base_modules: &[(&str, &[&str])] = &[
        ("LambdaSigil.CombinedKernel", &[]),
        (
            "LambdaSigil.SemanticKernel",
            &["LambdaSigil.CombinedKernel"],
        ),
        (
            "LambdaSigil.HostProfileKernel",
            &["LambdaSigil.CombinedKernel"],
        ),
        (
            "LambdaSigil.OccurrenceWire",
            &["LambdaSigil.HostProfileKernel"],
        ),
    ];
    let direct_dependencies = base_modules
        .iter()
        .chain(v9_modules.iter())
        .map(|(module, dependencies)| (*module, *dependencies))
        .collect::<std::collections::BTreeMap<&str, &[&str]>>();
    for (module, dependencies) in &direct_dependencies {
        assert_declared_imports_match_source(&lean_root, module, dependencies);
    }
    let transitive_dependencies = |module: &str| -> Vec<&str> {
        let mut closure = Vec::new();
        let mut pending = direct_dependencies
            .get(module)
            .unwrap_or_else(|| panic!("native module {module} has no declared imports"))
            .to_vec();
        while let Some(dependency) = pending.pop() {
            if closure.contains(&dependency) {
                continue;
            }
            closure.push(dependency);
            pending.extend_from_slice(direct_dependencies.get(dependency).unwrap_or_else(|| {
                panic!("native dependency {dependency} has no declared imports")
            }));
        }
        closure.sort_unstable();
        closure
    };
    let mut generated_v9 = Vec::with_capacity(v9_modules.len());
    for (module, _) in v9_modules {
        let owned_imports = transitive_dependencies(module)
            .into_iter()
            .map(|dependency| {
                (
                    dependency,
                    native_artifacts
                        .get(dependency)
                        .unwrap_or_else(|| panic!("native dependency {dependency} not built"))
                        .clone(),
                )
            })
            .collect::<Vec<_>>();
        let imports = owned_imports
            .iter()
            .map(|(name, path)| (*name, path.as_path()))
            .collect::<Vec<_>>();
        let (generated, object) = compile_lean_module(&lean_root, &out, module, &imports);
        println!(
            "cargo:rerun-if-changed={}/{}.lean",
            lean_root.display(),
            module.replace('.', "/")
        );
        generated_v9.push(generated);
        native_artifacts.insert(module, object);
    }

    let host_prefix = checked_output(
        Command::new("lake")
            .current_dir(&lean_root)
            .args(["env", "lean", "--print-prefix"]),
        "Lean prefix probe",
    );
    let host_prefix = PathBuf::from(host_prefix.trim());
    let host = env::var("HOST").expect("Cargo must provide HOST");
    let target = env::var("TARGET").expect("Cargo must provide TARGET");
    let prefix = if host == target {
        host_prefix
    } else {
        let supplied = env::var_os("SIGIL_LEAN_TARGET_PREFIX").unwrap_or_else(|| {
            panic!(
                "cross-compiling the mandatory Lean verifier from `{host}` to `{target}` requires \
                 SIGIL_LEAN_TARGET_PREFIX to name the exact pinned Lean runtime for `{target}`"
            )
        });
        PathBuf::from(supplied)
    };
    let include = prefix.join("include");
    let lib = prefix.join("lib/lean");
    let dependency_lib = prefix.join("lib");
    let init_archive = lib.join("libInit.a");
    let runtime_archive = lib.join("libleanrt.a");
    let gmp_archive = dependency_lib.join("libgmp.a");
    let uv_archive = dependency_lib.join("libuv.a");
    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let target_family = env::var("CARGO_CFG_TARGET_FAMILY").unwrap_or_default();
    // Lean's Linux distribution is built against LLVM's libc++ (its runtime archives reference
    // `std::__1::*`), not GNU libstdc++, and it ships the matching static archives beside
    // libgmp/libuv for exactly this static-link use. Linking `stdc++` there left every libc++
    // symbol in libleanrt.a undefined on a fresh Linux runner. macOS resolves the same symbols
    // from the system libc++, and MSVC uses the C++ runtime import library below.
    let links_lean_cxx_runtime = target_family == "unix" && target_os != "macos";
    let cxx_archives = [
        dependency_lib.join("libc++.a"),
        dependency_lib.join("libc++abi.a"),
    ];
    let mut required_paths = vec![
        include.clone(),
        init_archive.clone(),
        runtime_archive.clone(),
        gmp_archive.clone(),
        uv_archive.clone(),
    ];
    if links_lean_cxx_runtime {
        required_paths.extend(cxx_archives.iter().cloned());
    }
    for required in &required_paths {
        assert!(
            required.exists(),
            "target Lean prefix `{}` is missing `{}`",
            prefix.display(),
            required.display()
        );
    }

    let mut native_build = cc::Build::new();
    native_build
        .include(&include)
        // The verifier is a production security gate even when its Rust caller is built under
        // Cargo's debug/test profile.  Lean's generated C otherwise inherits OPT_LEVEL=0, making
        // the warm in-process gate measure an interpreter-like debug artifact rather than the
        // statically linked verifier shipped to users.  Keep this explicit and fingerprinted in
        // build.rs so every profile and platform compiles the exact checker at production
        // optimization without changing any decision procedure or rollout threshold.
        .opt_level(3)
        // Lean's generated C carries nothing worth a DWARF entry, yet under Cargo's dev/test
        // profile `cc` inherits DEBUG=true and emits several times the code size in debug
        // sections. On ELF targets that debug info is copied into every one of the ~200
        // workspace test binaries linking this archive, which is what pushed the hosted `test`
        // runner past its disk mid-link (ld SIGBUS). The native verifier objects are therefore
        // built without debug info on every profile; optimization level and decision
        // procedure are unchanged.
        .debug(false)
        .file(&generated_kernel)
        .file(&generated_semantic)
        .file(&generated_host_profile)
        .file(&generated_occurrence_wire)
        .files(&generated_v9)
        .file(&shim)
        .warnings(false)
        // Apple `/usr/bin/ar` does not implement GNU's `D` modifier. `cc` probes it and
        // correctly falls back to `ZERO_AR_DATE=1`, but forwarding the expected probe failure
        // as a Cargo warning makes clean macOS builds look broken. Suppress command-probe
        // warnings only; deterministic archive construction and hard build failures are unchanged.
        .cargo_warnings(false);
    native_build.compile("sigil_combined_lean");

    println!("cargo:rustc-link-search=native={}", lib.display());
    println!(
        "cargo:rustc-link-search=native={}",
        dependency_lib.display()
    );
    if env::var("CARGO_CFG_TARGET_ENV").as_deref() == Ok("msvc") {
        // The official Lean Windows distribution deliberately ships GNU-style
        // `lib*.a` COFF archives. `rustc-link-lib` asks the MSVC linker for
        // `*.lib`, so pass the verified archive paths verbatim instead.
        for archive in [init_archive, runtime_archive, gmp_archive, uv_archive] {
            println!("cargo:rustc-link-arg={}", archive.display());
        }
        println!("cargo:rustc-link-lib=msvcprt");
    } else {
        println!("cargo:rustc-link-lib=static=Init");
        println!("cargo:rustc-link-lib=static=leanrt");
        println!("cargo:rustc-link-lib=static=gmp");
        println!("cargo:rustc-link-lib=static=uv");
    }
    if target_os == "macos" {
        println!("cargo:rustc-link-lib=c++");
    } else if links_lean_cxx_runtime {
        // Static, from the pinned Lean prefix: the only C++ runtime that matches the pinned
        // Lean runtime archives. Unwinding stays on the platform libgcc_s that Rust links.
        println!("cargo:rustc-link-lib=static=c++");
        println!("cargo:rustc-link-lib=static=c++abi");
    }
}
