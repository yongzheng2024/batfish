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
        // reachability scenario1
        NetworkId networkId = new NetworkId("5e368f10-32db-4465-95fa-d9b4d75e419f");

        // snapshot-reachability-0001: reachability true (without interface's access-list)
        SnapshotId snapshotId = new SnapshotId("94a6ae45-b6a5-4946-a665-6756d9fb7517");
        // snapshot-reachability-0002: reachability false (without interface's access-list)
        // SnapshotId snapshotId = new SnapshotId("dccc87a7-7b0f-4ccb-98b1-1747034bfc8d");

        // snapshot-reachability-0003: reachability true（with interface's access-list)
        // SnapshotId snapshotId = new SnapshotId("2eaa248d-8e42-4858-8a72-a402274ab7cd");
        // snapshot-reachability-0004: reachability false (with interface's access-list)
        // SnapshotId snapshotId = new SnapshotId("d4a14ef1-3149-4a82-baeb-37f65dd64f0e");

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
        // test case 0001
        // question.setFinalNodeRegex("as1border1");
        // question.setFinalIfaceRegex("GigabitEthernet1/0");
        // test case 0002
        question.setFinalNodeRegex("as1core1");
        question.setFinalIfaceRegex("GigabitEthernet1/0");
        // question.setFinalNodeRegex("as3border2");
        // question.setFinalIfaceRegex("GigabitEthernet1/0");
        // question.setFailures(1);

        final AnswerElement answer = Answerer.create(question, _batfish).answer(_batfish.getSnapshot());
        assertThat(answer, instanceOf(SmtReachabilityAnswerElement.class));

        final SmtReachabilityAnswerElement smtAnswer = (SmtReachabilityAnswerElement) answer;
        assertThat(smtAnswer, hasVerificationResult(hasIsVerified(true)));
    }
}
