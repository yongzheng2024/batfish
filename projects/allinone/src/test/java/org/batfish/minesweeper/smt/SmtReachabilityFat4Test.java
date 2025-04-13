package org.batfish.minesweeper.smt;

// import static java.util.Collections.singleton;

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

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.SortedMap;
import java.util.TreeMap;

import static org.batfish.minesweeper.smt.matchers.SmtReachabilityAnswerElementMatchers.hasVerificationResult;
import static org.batfish.minesweeper.smt.matchers.VerificationResultMatchers.hasIsVerified;
import static org.hamcrest.Matchers.instanceOf;
import static org.junit.Assert.assertThat;

public class SmtReachabilityFat4Test {
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
        NetworkId networkId = new NetworkId("3a1e0980-ee04-44b6-baa7-0b25cbdd23d2");
        SnapshotId snapshotId = new SnapshotId("471504bc-b6ae-4d83-95a1-55bd91af8029");
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
        // question.setDstIps(new IpWildcard("70.0.79.0"));
        // question.setIngressNodeRegex("");
        // question.setFinalNodeRegex("");
        // question.setFinalIfaceRegex("");
        // question.setFailures(1);

        question.setFinalIfaceRegex(".*");

        final AnswerElement answer = Answerer.create(question, _batfish).answer(_batfish.getSnapshot());
        assertThat(answer, instanceOf(SmtReachabilityAnswerElement.class));

        final SmtReachabilityAnswerElement smtAnswer = (SmtReachabilityAnswerElement) answer;
        System.out.println();
        System.out.println("SMT encoding finished.");
        assertThat(smtAnswer, hasVerificationResult(hasIsVerified(true)));
    }
}
