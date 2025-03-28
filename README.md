### <b>Install</b>

Batfish/Minesweeper depend on the following software.

* OpenJDK 11
* Bazel
* Z3
* Pytbatfish (modified by yongzheng)

You can directly run the command `./install.sh` to install these software in Ubuntu22.04 (tested) or macOS (TODO, error).

You must modified two directory pach according to your practical path.

* `/PATH-TO/batfish/.bazelrc`

```sh
# Test targets are required to depend on our junit rather than using the one provided by Bazel
build --sandbox_writable_path=/home/deza/codes/batfish/smts/ \
      --action_env=SMT_DIRECTORY_PREFIX=/home/deza/codes/batfish/smts/ \
      --explicit_java_test_deps

# /home/deza/codes/batfish -> /PATH-TO/batfish
```

* `/PATH-TO/batfish/projects/allinone/src/test/java/org/batfish/minesweeper/smt/SmtReachabilityTest.java`

```java
/** Replace the path with your actual project path. */
Path path = Paths.get("/home/deza/codes/batfish/containers");
Batfish batfish = BatfishTestUtils.initBatfish(new TreeMap<>(), path);

// /home/deza/codes/batfish -> /PATH-TO/batfish
```

### <b>Partical Directory Structure</b>

* projects (source code)
* tools (build and run scripts)
* networks (network configuration files)
* tests/test (test case files via pybatfish)
* smts (smt encoding files)
* install.sh (intall all required software dependencies)
* .bazelversion (bazel configuration file)
* .bazelrc (bazel configuration file)

### <b>Test</b>

> [PyBatfish usage document](https://pybatfish.readthedocs.io/en/latest/getting_started.html) <br>
> [PyBatfish interact with the Batfish service](https://pybatfish.readthedocs.io/en/latest/notebooks/interacting.html#)

#### Test Case 1 via Pybatfish

Open two terminals: one for running the Batfish service, and other for running a Pybatfish test case.

In the first terminal, start the Batfish service:
```sh
cd /PATH-TO/batfish
tools/bazel_run.sh
```

In the second terminal, run the Pybatfish test case:
```sh
cd /PATH-TO/tests/test
python3 test_routing_policies_0001.py
```

#### Test Case 2 SmtReachabilityTest

Just open one terminal, and run test case script.

```sh
cd /PATH-TO/batfish
tools/bazel_test_SmtReachabilityTest.sh
```

### <b>Configure Intellij IDEA</b>

> [IntelliJ IDEA configuration document](https://github.com/batfish/batfish/tree/master/docs/intellij_setup)

You can install plugins `Bazel For Intellij` and `Bazel (EAP)`. Then import the batfish directory from `file` - `import bazel project`.

You can configure bazel command in `Run/Debug configurations` according to following steps (modify `/PATH-TO/batfish` to your root directory of batfish).

```txt
* Target expression (Java\_binary handled by Java Handler)
    - //projects/allinone:allinone\_main
* Bazel command
    - run
* Bazel flags
    - --jvmopt=-Xmx12g
    - --jvmopt=-Dlog4j2.configurationFile=tools/log4j2.yaml
    - --java\_runtime\_version=11
    - --run\_under="cd /PATH-TO/batfish &&"
* Executable flags
    - -runclient
    - false
    - -coordinatorargs
    - "-templatedirs ./questions"
```
