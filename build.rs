fn main() {
    print!(
        "cargo:rustc-env=GIT_COMMIT={}",
        std::str::from_utf8(
            &std::process::Command::new("git")
                .arg("rev-parse")
                .arg("HEAD")
                .output()
                .expect("failed to run git")
                .stdout
        )
        .unwrap()
    );
}
