package org.batfish.minesweeper.smt;

// import static java.util.Collections.singleton;
import static org.batfish.minesweeper.smt.matchers.SmtReachabilityAnswerElementMatchers.hasVerificationResult;
// import static org.batfish.minesweeper.smt.matchers.VerificationResultMatchers.hasFailures;
import static org.batfish.minesweeper.smt.matchers.VerificationResultMatchers.hasIsVerified;
// import static org.hamcrest.Matchers.allOf;
import static org.hamcrest.Matchers.instanceOf;
import static org.junit.Assert.assertThat;

// import com.google.common.collect.ImmutableSet;
import java.io.IOException;
import java.util.SortedMap;
import org.batfish.common.Answerer;
import org.batfish.common.NetworkSnapshot;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.identifiers.NetworkId;
import org.batfish.identifiers.SnapshotId;
import org.batfish.main.Batfish;
import org.batfish.main.BatfishTestUtils;
import org.batfish.minesweeper.answers.SmtReachabilityAnswerElement;
import org.batfish.minesweeper.question.SmtReachabilityQuestionPlugin.ReachabilityQuestion;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import java.nio.file.*;
import java.util.TreeMap;

public class SmtReachabilityTest {
    @Rule public TemporaryFolder _temp = new TemporaryFolder();

    private Batfish _batfish;
    // private NetworkSnapshot _snapshot;
    private Configuration _dstNode;
    private Configuration _srcNode;
    private String _failureDesc;

    @Before
    public void setup() throws IOException {
        // Files.copy(sourcePath, destinationPath, StandardCopyOption.REPLACE_EXISTING);

        /** Replace the path with your actual project path. */
        Path path = Paths.get("/home/deza/codes/batfish/containers");
        Batfish batfish = BatfishTestUtils.initBatfish(new TreeMap<>(), path);

        /** Replace network ID and snapshot ID with the actual ID at your local disk. */
        NetworkId networkId = new NetworkId("d6a9222c-562d-4a81-a8b9-17c55d800dbd");

        // reachability true (without interface's access-list)
        SnapshotId snapshotId = new SnapshotId("37394fd6-1712-4961-850f-bb0527094100");
        // reachability false (without interface's access-list)
        // SnapshotId snapshotId = new SnapshotId("14c875ec-f730-4267-b628-64a27194b77a");

        // reachability true（with interface's access-list)
        // SnapshotId snapshotId = new SnapshotId("e551f896-7b2c-49e6-aad2-928e63f38a3f");
        // reachability false (with interface's access-list)
        // SnapshotId snapshotId = new SnapshotId("f94b2191-a590-42ed-a7f8-a45174482734");

        NetworkSnapshot snapshot = new NetworkSnapshot(networkId, snapshotId);
        SortedMap<String, Configuration> configs = batfish.loadConfigurations(snapshot);
        _batfish = BatfishTestUtils.getBatfish(configs, _temp);
        // SortedMap<String, Configuration> configs = _batfish.loadConfigurations(_batfish.getSnapshot());
        // _dstNode = configs.get(TwoNodeNetworkWithTwoLinks.DST_NODE);
        // _srcNode = configs.get(TwoNodeNetworkWithTwoLinks.SRC_NODE);
        // _failureDesc = String.format("link(%s,%s)", _dstNode.getHostname(), _srcNode.getHostname());
    }

    /**
     * Test that with one failure, both links between the two nodes are down, so no _dstIp is
     * reachable from the source. The reachability property is false under 1 failure.
     */
    @Test
    public void testOneFailure() {
        final ReachabilityQuestion question = new ReachabilityQuestion();
        question.setIngressNodeRegex("as2border1");
        // question.setFinalNodeRegex("as1border1");
        // question.setFinalIfaceRegex("GigabitEthernet1/0");
        question.setFinalNodeRegex("as1core1");
        question.setFinalIfaceRegex("GigabitEthernet1/0");
        // question.setFailures(1);

        final AnswerElement answer = Answerer.create(question, _batfish).answer(_batfish.getSnapshot());
        assertThat(answer, instanceOf(SmtReachabilityAnswerElement.class));

        final SmtReachabilityAnswerElement smtAnswer = (SmtReachabilityAnswerElement) answer;
        assertThat(smtAnswer, hasVerificationResult(hasIsVerified(true)));
    }
}
