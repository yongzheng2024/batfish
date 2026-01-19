package org.batfish.minesweeper.smt;

import org.batfish.common.Answerer;
// import org.batfish.common.NetworkSnapshot;
import org.batfish.datamodel.IpWildcard;
import org.batfish.datamodel.Zone;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.main.Batfish;
import org.batfish.main.BatfishTestUtils;
import org.batfish.main.TestrigText;
import org.batfish.minesweeper.answers.SmtOneAnswerElement;
import org.batfish.question.routes.RoutesQuestion;
import org.batfish.question.routes.RoutesAnswerer;
import org.batfish.minesweeper.answers.SmtReachabilityAnswerElement;
import org.batfish.minesweeper.question.SmtReachabilityQuestionPlugin.ReachabilityQuestion;
import org.batfish.minesweeper.question.SmtBoundedLengthQuestionPlugin.BoundedLengthQuestion;
import org.batfish.minesweeper.question.SmtBlackholeQuestionPlugin.BlackholeQuestion;
import org.batfish.minesweeper.utils.ConfigLoader;
import org.batfish.minesweeper.utils.RibPrinter;
import static org.batfish.minesweeper.smt.Encoder.createOutputDirectory;

import static org.hamcrest.Matchers.instanceOf;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.is;

import org.junit.rules.TemporaryFolder;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;

import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.io.IOException;
import java.time.ZoneId;
import java.util.Set;
import java.util.SortedMap;

import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;

import com.google.devtools.build.runfiles.Runfiles;

public class SmtReachabilityTest {
    @Rule public TemporaryFolder _temp = new TemporaryFolder();

    private Batfish _batfish;
    // private NetworkSnapshot _snapshot;

    // printers for output files
    private PrintWriter _bgpRouteWriter;
    private PrintWriter _dataPlaneWriter;

    @Before
    public void setup() throws IOException {
        System.out.println();
        // Beijing timezone
        ZoneId chinaZone = ZoneId.of("Asia/Shanghai");
        // Current time in Beijing
        LocalDateTime beijingTime = LocalDateTime.now(chinaZone);
        // Format output
        DateTimeFormatter formatter = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss");
        String formattedNow = beijingTime.format(formatter);
        // Output the beijing time for the beginning of the test running
        System.out.println("=== Running test at " + formattedNow + " (Beijing Time) ===");

        // create a smt output directory
        String outputDir = createOutputDirectory();
        String outputBgpRouteFileName = outputDir + "/0_ebgp_routes.txt";
        String outputDataPlaneFileName = outputDir + "/0_data_plane.txt";
        File outputBgpRouteFile = new File(outputBgpRouteFileName);
        File outputDataPlaneFile = new File(outputDataPlaneFileName);
        try {
            _bgpRouteWriter = new PrintWriter(new FileWriter(outputBgpRouteFile, true));
            _dataPlaneWriter = new PrintWriter(new FileWriter(outputDataPlaneFile, true));
        } catch (IOException e) {
            System.err.println("Error: Unable to create file: " + e.getMessage());
        }

        // read the configurations from the filesystem
        Runfiles runfiles = Runfiles.create();

        // String configPath = runfiles.rlocation("batfish/networks/userstudy_network");
        // String configPath = runfiles.rlocation("batfish/networks/userstudy_network_hard");
        // String configPath = runfiles.rlocation("batfish/networks/userstudy_network_accessment");
        // String configPath = runfiles.rlocation("batfish/networks/userstudy_network_accessment_intro");
        // String configPath = runfiles.rlocation("batfish/networks/userstudy_network_coursera");
        // String configPath = runfiles.rlocation("batfish/networks/symbolic_configuration_network");

        // -------------------------------------------------------------

        // String configPath = runfiles.rlocation("batfish/networks/testing_networks/sub-prefixes_0001");
        // String configPath = runfiles.rlocation("batfish/networks/testing_networks/sub-prefixes_0002");
        // String configPath = runfiles.rlocation("batfish/networks/testing_networks/deny_permit");
        // String configPath = runfiles.rlocation("batfish/networks/testing_networks/deny_community");

        // -------------------------------------------------------------

        // String configPath = runfiles.rlocation("batfish/benchmarks/FatTrees/fattree4pol");
        // String configPath = runfiles.rlocation("batfish/benchmarks/FatTrees/fattree8pol");
        // String configPath = runfiles.rlocation("batfish/benchmarks/FatTrees/fattree12pol");
        // String configPath = runfiles.rlocation("batfish/benchmarks/FatTrees/fattree16pol");
        // String configPath = runfiles.rlocation("batfish/benchmarks/FatTrees/fattree20pol");
        // String configPath = runfiles.rlocation("batfish/benchmarks/FatTrees/fattree24pol");
        // String configPath = runfiles.rlocation("batfish/benchmarks/FatTrees/fattree28pol");
        // String configPath = runfiles.rlocation("batfish/benchmarks/FatTrees/fattree32pol");

        TestrigText _testrig = loadConfigurations(configPath);
        _batfish = BatfishTestUtils.getBatfishFromTestrigText(_testrig, _temp);

         // compute data plane for printing RIBs before
         _batfish.computeDataPlane(_batfish.getSnapshot(), _bgpRouteWriter);
         // print RIBs of the data plane in formal format
         RoutesQuestion routesQuestion = new RoutesQuestion();
         RoutesAnswerer routesAnswerer = new RoutesAnswerer(routesQuestion, _batfish);
         AnswerElement routesAnswer = routesAnswerer.answer(_batfish.getSnapshot());
         RibPrinter.printRouteTable(routesAnswer, _dataPlaneWriter);
    }

    /**
     * Test network property: Reachability (or Isolation with negated) via SMT.
     * You can set node failures (or not) or edge failures (or not).
     */
    @Test
    public void testReachability() {
        final ReachabilityQuestion question = new ReachabilityQuestion();

        // Specification 1: Customer reachability
        // question.setIngressNodeRegex("customer");
        // question.setFinalNodeRegex("isp1");
        // IpWildcard ipWildcard = IpWildcard.parse("198.51.100.0/24");
        // question.setDstIps(Set.of(ipWildcard));

        // Specification 2: No transit
        // question.setIngressNodeRegex("isp2");
        // question.setFinalNodeRegex("isp1");
        // IpWildcard ipWildcard = IpWildcard.parse("192.0.2.0/24");
        // question.setDstIps(Set.of(ipWildcard));
        // question.setNegate(true);
        //
        // question.setIngressNodeRegex("isp2");
        // question.setFinalNodeRegex("isp1");
        // IpWildcard ipWildcard = IpWildcard.parse("198.51.100.0/24");
        // question.setDstIps(Set.of(ipWildcard));
        // question.setNegate(true);
        //
        // question.setIngressNodeRegex("isp1");
        // question.setFinalNodeRegex("isp2");
        // IpWildcard ipWildcard = IpWildcard.parse("203.0.113.0/24");
        // question.setDstIps(Set.of(ipWildcard));
        // question.setNegate(true);

        // Specification 3: ECMP reachability
        // question.setIngressNodeRegex("r3");
        // question.setFinalNodeRegex("isp2");
        // IpWildcard ipWildcard = IpWildcard.parse("203.0.113.0/24");
        // question.setDstIps(Set.of(ipWildcard));

        // Specification 4: Private prefix filtering
        // question.setIngressNodeRegex("r3");
        // question.setFinalNodeRegex("customer");
        // IpWildcard ipWildcard = IpWildcard.parse("192.168.128.0/24");
        // question.setDstIps(Set.of(ipWildcard));
        // question.setNegate(true);
        //
        // question.setIngressNodeRegex("r3");
        // question.setFinalNodeRegex("customer");
        // IpWildcard ipWildcard = IpWildcard.parse("192.168.129.0/24");
        // question.setDstIps(Set.of(ipWildcard));
        // question.setNegate(true);

        // -------------------------------------------------------------

        // Specification 01: Qualification test 1
        // question.setIngressNodeRegex("customer");
        // question.setFinalNodeRegex("isp1");
        // IpWildcard ipWildcard = IpWildcard.parse("192.0.2.0/24");
        // question.setDstIps(Set.of(ipWildcard));

        // Specification 02: Qualification test 2
        // question.setIngressNodeRegex("customer");
        // question.setFinalNodeRegex("isp1");
        // IpWildcard ipWildcard = IpWildcard.parse("198.51.100.0/24");
        // question.setDstIps(Set.of(ipWildcard));
        // question.setNegate(true);

        // -------------------------------------------------------------

        // Specification 01: Qualification test 1 (for introduction)
        // question.setIngressNodeRegex("customer");
        // question.setFinalNodeRegex("isp1");
        // IpWildcard ipWildcard = IpWildcard.parse("10.0.0.0/8");
        // question.setDstIps(Set.of(ipWildcard));

        // Specification 02: Qualification test 2 (for introduction)
        // question.setIngressNodeRegex("customer");
        // question.setFinalNodeRegex("isp1");
        // IpWildcard ipWildcard = IpWildcard.parse("192.168.0.0/16");
        // question.setDstIps(Set.of(ipWildcard));
        // question.setNegate(true);

        // -------------------------------------------------------------

        // Specification 01: Coursera test 1
        // question.setIngressNodeRegex("r1");
        // question.setFinalNodeRegex("customer");
        // IpWildcard ipWildcard = IpWildcard.parse("172.16.0.0/12");
        // question.setDstIps(Set.of(ipWildcard));

        // -------------------------------------------------------------

        // sub-prefixes
        // question.setIngressNodeRegex("r2");
        // question.setFinalNodeRegex("isp1");
        // IpWildcard ipWildcard = IpWildcard.parse("10.0.0.0/8");
        // question.setDstIps(Set.of(ipWildcard));

        // -------------------------------------------------------------

        // deny-permit and permit-permit
        // question.setIngressNodeRegex("customer");
        // question.setFinalNodeRegex("isp1");
        // IpWildcard ipWildcard = IpWildcard.parse("192.168.0.0/16");
        // question.setDstIps(Set.of(ipWildcard));

        // -------------------------------------------------------------

        // FatTree benchmarks - fattree04pol
        // question.setIngressNodeRegex(".*");
        // question.setFinalNodeRegex("edge-19");
        // IpWildcard ipWildcard = IpWildcard.parse("70.0.19.0/24");
        // question.setDstIps(Set.of(ipWildcard));

        // FatTree benchmarks - fattree08pol
        // question.setIngressNodeRegex(".*");
        // question.setFinalNodeRegex("edge-79");
        // IpWildcard ipWildcard = IpWildcard.parse("70.0.79.0/24");
        // question.setDstIps(Set.of(ipWildcard));

        // FatTree benchmarks - fattree12pol
        // question.setIngressNodeRegex(".*");
        // question.setFinalNodeRegex("edge-179");
        // IpWildcard ipWildcard = IpWildcard.parse("70.0.179.0/24");
        // question.setDstIps(Set.of(ipWildcard));

        // FatTree benchmarks - fattree16pol
        // question.setIngressNodeRegex(".*");
        // question.setFinalNodeRegex("edge-319");
        // IpWildcard ipWildcard = IpWildcard.parse("70.1.63.0/24");
        // question.setDstIps(Set.of(ipWildcard));

        // FatTree benchmarks - fattree20pol
        // question.setIngressNodeRegex(".*");
        // question.setFinalNodeRegex("edge-499");
        // IpWildcard ipWildcard = IpWildcard.parse("70.1.243.0/24");
        // question.setDstIps(Set.of(ipWildcard));

        // FatTree benchmarks - fattree24pol
        // question.setIngressNodeRegex(".*");
        // question.setFinalNodeRegex("edge-719");
        // IpWildcard ipWildcard = IpWildcard.parse("70.2.207.0/24");
        // question.setDstIps(Set.of(ipWildcard));

        // FatTree benchmarks - fattree28pol
        // question.setIngressNodeRegex(".*");
        // question.setFinalNodeRegex("edge-979");
        // IpWildcard ipWildcard = IpWildcard.parse("70.3.211.0/24");
        // question.setDstIps(Set.of(ipWildcard));

        // FatTree benchmarks - fattree32pol
        // question.setIngressNodeRegex(".*");
        // question.setFinalNodeRegex("edge-1279");
        // IpWildcard ipWildcard = IpWildcard.parse("70.4.255.0/24");
        // question.setDstIps(Set.of(ipWildcard));

        // -------------------------------------------------------------

        final AnswerElement answer = Answerer.create(question, _batfish).answer(_batfish.getSnapshot());
        assertThat(answer, instanceOf(SmtReachabilityAnswerElement.class));

        final SmtReachabilityAnswerElement smtAnswer = (SmtReachabilityAnswerElement) answer;
        assertThat(smtAnswer.getResult().isVerified(), is(true));
    }

    /**
     * Test network property: Bounded Length via SMT.
     * You can set node failures (or not) or edge failures (or not).
     */
    /*
    @Test
    public void testBoundedLength() {
        final BoundedLengthQuestion question = new BoundedLengthQuestion();
        question.setBound(3);
        question.setIngressNodeRegex("customer1");
        question.setFinalNodeRegex("isp1");
        question.setFinalIfaceRegex("GigabitEthernet3/0");

        final AnswerElement answer = Answerer.create(question, _batfish).answer(_batfish.getSnapshot());
        assertThat(answer, instanceOf(SmtOneAnswerElement.class));

        final SmtOneAnswerElement smtAnswer = (SmtOneAnswerElement) answer;
        assertThat(smtAnswer.getResult().isVerified(), is(true));
    }
     */

    /**
     * Test network property: Bounded Length via SMT.
     * You can set node failures (or not) or edge failures (or not).
     */
    /*
    @Test
    public void testBlackhole() {
        final BlackholeQuestion question = new BlackholeQuestion();
        // question.setIngressNodeRegex("customer1");
        // question.setFinalNodeRegex("isp1");
        // question.setFinalIfaceRegex("GigabitEthernet3/0");

        final AnswerElement answer = Answerer.create(question, _batfish).answer(_batfish.getSnapshot());
        assertThat(answer, instanceOf(SmtOneAnswerElement.class));

        final SmtOneAnswerElement smtAnswer = (SmtOneAnswerElement) answer;
        assertThat(smtAnswer.getResult().isVerified(), is(true));
    }
     */

    /**
     * Load configurations, hosts and iptables files from specified directory.
     *
     * @param configPathStr base path to the directory containing "configs", "hosts", and "iptables" subdirectories.
     * @return TestrigText object containing all loaded file bytes.
     */
    public static TestrigText loadConfigurations(String configPathStr) {
        try {
            // Ensure directory path ends with separator
            if (!configPathStr.endsWith("/") && !configPathStr.endsWith("\\")) {
                configPathStr += System.getProperty("file.separator");
            }

            SortedMap<String, byte[]> configurationsBytes =
                ConfigLoader.loadAllFiles(configPathStr + "configs", ".cfg");
            SortedMap<String, byte[]> hostsBytes =
                ConfigLoader.loadAllFiles(configPathStr + "hosts", ".json");
            SortedMap<String, byte[]> iptablesBytes =
                ConfigLoader.loadAllFiles(configPathStr + "iptables", ".iptables");

            return TestrigText.builder()
                .setConfigurationBytes(configurationsBytes)
                .setHostsBytes(hostsBytes)
                .setIptablesBytes(iptablesBytes)
                .build();

        } catch (IOException e) {
            System.err.println("Failed to load configurations from " + configPathStr + ": " + e.getMessage());
            return TestrigText.builder().build();
        }
    }
}
