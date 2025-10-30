### <b>Install</b>

Batfish/Minesweeper require the following software dependencies:

* OpenJDK 11
* Bazel

To install these dependencies, simply run the following command.
> This script has been tested on Ubuntu 22.04 and Ubuntu 24.04.

```bash
$ ./install.sh
```

---

### <b>Test</b>

To verify that your environment is set up correctly, simply run the following command.
If the script runs successfully, your environment is properly configured.

```bash
$ ./tools/bazel_test_SmtReachabilityTest.sh
```

---

### <b>Configure IntelliJ IDEA</b>

Install the following plugins in IntelliJ IDEA:
* Bazel for IntelliJ
* Bazel (EAP)

Import the Batfish/Minesweeper project:
* Go to `File` → `Import Bazel Project...`
* Select the Batfish/Minesweeper project directory

Configure `Bazel Command` in `Run/Debug Configurations`:

```txt
* Target expression (Java\_binary handled by Java Handler):
    + //projects/allinone:smt_tests

* Bazel handler:
    JVM Compatible (Binary or Test)

* Bazel command:
    test

* Bazel flags
    --test_filter=org.batfish.minesweeper.smt.SmtReachabilityTest#
    --cache_test_results=no
```
