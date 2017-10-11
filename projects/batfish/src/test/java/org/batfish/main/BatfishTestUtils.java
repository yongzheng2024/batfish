package org.batfish.main;

import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;
import java.io.IOException;
import java.nio.file.Path;
import java.util.Collections;
import java.util.Map;
import java.util.SortedMap;
import java.util.TreeMap;
import javax.annotation.Nullable;
import org.apache.commons.collections4.map.LRUMap;
import org.batfish.common.BatfishException;
import org.batfish.common.BatfishLogger;
import org.batfish.common.BfConsts;
import org.batfish.common.util.CommonUtil;
import org.batfish.config.Settings;
import org.batfish.config.Settings.EnvironmentSettings;
import org.batfish.config.Settings.TestrigSettings;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.ConfigurationFormat;
import org.batfish.datamodel.DataPlane;
import org.batfish.datamodel.Interface;
import org.batfish.datamodel.collections.BgpAdvertisementsByVrf;
import org.batfish.datamodel.collections.RoutesByVrf;
import org.junit.rules.TemporaryFolder;

public class BatfishTestUtils {

  private static Cache<TestrigSettings, SortedMap<String, Configuration>> makeTestrigCache() {
    return CacheBuilder.newBuilder().maximumSize(5).weakValues().build();
  }

  private static Map<EnvironmentSettings, SortedMap<String, BgpAdvertisementsByVrf>>
      makeEnvBgpCache() {
    return Collections.synchronizedMap(new LRUMap<>(4));
  }

  private static Map<EnvironmentSettings, SortedMap<String, RoutesByVrf>> makeEnvRouteCache() {
    return Collections.synchronizedMap(new LRUMap<>(4));
  }

  private static Cache<TestrigSettings, DataPlane> makeDataPlaneCache() {
    return CacheBuilder.newBuilder().maximumSize(2).weakValues().build();
  }

  private static Batfish initBatfish(
      SortedMap<String, Configuration> configurations, @Nullable TemporaryFolder tempFolder)
      throws IOException {
    Settings settings = new Settings(new String[] {});
    settings.setLogger(new BatfishLogger("debug", false));
    final Cache<TestrigSettings, SortedMap<String, Configuration>> testrigs = makeTestrigCache();

    if (!configurations.isEmpty()) {
      Path containerDir = tempFolder.newFolder("container").toPath();
      settings.setContainerDir(containerDir);
      settings.setTestrig("tempTestrig");
      settings.setEnvironmentName("tempEnvironment");
      Batfish.initTestrigSettings(settings);
      settings.getBaseTestrigSettings().getSerializeIndependentPath().toFile().mkdirs();
      settings.getBaseTestrigSettings().getEnvironmentSettings().getEnvPath().toFile().mkdirs();
      testrigs.put(settings.getBaseTestrigSettings(), configurations);
      settings.setActiveTestrigSettings(settings.getBaseTestrigSettings());
    }
    Batfish batfish =
        new Batfish(
            settings, testrigs, makeDataPlaneCache(), makeEnvBgpCache(), makeEnvRouteCache());
    batfish.setMonotonicCache(true);
    return batfish;
  }

  private static Batfish initBatfishFromTestrigText(
      SortedMap<String, String> configurationText,
      SortedMap<String, String> bgpTablesText,
      SortedMap<String, String> hostsText,
      SortedMap<String, String> iptablesFilesText,
      SortedMap<String, String> routingTablesText,
      @Nullable TemporaryFolder tempFolder)
      throws IOException {
    Settings settings = new Settings(new String[] {});
    settings.setLogger(new BatfishLogger("debug", false));
    settings.setDisableUnrecognized(true);
    Path containerDir = tempFolder.newFolder("container").toPath();
    settings.setContainerDir(containerDir);
    settings.setTestrig("tempTestrig");
    settings.setEnvironmentName("tempEnvironment");
    Batfish.initTestrigSettings(settings);
    Path testrigPath = settings.getBaseTestrigSettings().getTestRigPath();
    Path configsDir = testrigPath.resolve(BfConsts.RELPATH_CONFIGURATIONS_DIR);
    Path awsDir = testrigPath.resolve(BfConsts.RELPATH_AWS_VPC_CONFIGS_DIR);
    Path bgpTablesDir =
        settings.getBaseTestrigSettings().getEnvironmentSettings().getEnvironmentBgpTablesPath();
    Path hostConfigsDir = testrigPath.resolve(BfConsts.RELPATH_HOST_CONFIGS_DIR);
    Path iptablesDir = testrigPath.resolve("iptables");
    Path routingTablesDir =
        settings
            .getBaseTestrigSettings()
            .getEnvironmentSettings()
            .getEnvironmentRoutingTablesPath();
    configsDir.toFile().mkdirs();
    awsDir.toFile().mkdirs();
    bgpTablesDir.toFile().mkdirs();
    hostConfigsDir.toFile().mkdirs();
    iptablesDir.toFile().mkdirs();
    routingTablesDir.toFile().mkdirs();
    settings.setActiveTestrigSettings(settings.getBaseTestrigSettings());
    configurationText.forEach(
        (filename, content) -> {
          Path filePath = configsDir.resolve(filename);
          CommonUtil.writeFile(filePath, content);
        });
    bgpTablesText.forEach(
        (filename, content) -> {
          Path filePath = bgpTablesDir.resolve(filename);
          CommonUtil.writeFile(filePath, content);
        });
    hostsText.forEach(
        (filename, content) -> {
          Path filePath = hostConfigsDir.resolve(filename);
          CommonUtil.writeFile(filePath, content);
        });
    iptablesFilesText.forEach(
        (filename, content) -> {
          Path filePath = iptablesDir.resolve(filename);
          CommonUtil.writeFile(filePath, content);
        });
    routingTablesText.forEach(
        (filename, content) -> {
          Path filePath = routingTablesDir.resolve(filename);
          CommonUtil.writeFile(filePath, content);
        });

    Batfish batfish =
        new Batfish(
            settings,
            makeTestrigCache(),
            makeDataPlaneCache(),
            makeEnvBgpCache(),
            makeEnvRouteCache());
    batfish.serializeVendorConfigs(
        testrigPath, settings.getBaseTestrigSettings().getSerializeVendorPath());
    batfish.serializeIndependentConfigs(
        settings.getBaseTestrigSettings().getSerializeVendorPath(),
        settings.getBaseTestrigSettings().getSerializeIndependentPath());
    return batfish;
  }

  /**
   * Get a configuration object with the given interfaces
   *
   * @param nodeName Host name for the configuration
   * @param configFormat Configuration format
   * @param interfaceNames All interface names to be included
   * @return A new configuration
   */
  public static Configuration createTestConfiguration(
      String nodeName, ConfigurationFormat configFormat, String... interfaceNames) {
    Configuration config = new Configuration(nodeName);
    config.setConfigurationFormat(configFormat);
    for (String interfaceName : interfaceNames) {
      config.getInterfaces().put(interfaceName, new Interface(interfaceName, config));
    }
    return config;
  }

  /**
   * Prepares a default scenario from provided configs and returns a Batfish pointing to it.
   *
   * @param testrigResourcePrefix Denotes the resource path to the input testrig
   * @param configFilenames The names of the configuration files. The filename for each
   *     configuration should be identical to the hostname declared therein.
   * @param bgpFilenames The names of the routing table files. The filename for each routing table
   *     should be identical to the hostname of the corresponding configuration.
   * @param hostFilenames The names of the host configuration files. The filename for each host
   *     configuration should be identical to the hostname declared therein.
   * @param iptablesFilenames The names of the iptables configuration files. The filename for each
   *     iptables configuration should match that declared in the corresponding host file.
   * @param rtFilenames The names of the bgp table files. The filename for each bgp table should be
   *     identical to the hostname of the corresponding configuration.
   * @param tempFolder Temporary folder in which to place the container for the scenario
   * @return A Batfish pointing to the newly prepared scenario.
   */
  public static Batfish getBatfishFromTestrigResource(
      String testrigResourcePrefix,
      String[] configFilenames,
      String[] bgpFilenames,
      String[] hostFilenames,
      String[] iptablesFilenames,
      String[] rtFilenames,
      @Nullable TemporaryFolder tempFolder)
      throws IOException {
    SortedMap<String, String> configurationsText =
        readTestrigResources(
            testrigResourcePrefix, BfConsts.RELPATH_CONFIGURATIONS_DIR, configFilenames);
    SortedMap<String, String> bgpTablesText =
        readTestrigResources(
            testrigResourcePrefix, BfConsts.RELPATH_ENVIRONMENT_BGP_TABLES, bgpFilenames);
    SortedMap<String, String> hostFilesText =
        readTestrigResources(
            testrigResourcePrefix, BfConsts.RELPATH_HOST_CONFIGS_DIR, hostFilenames);
    SortedMap<String, String> iptablesFilesText =
        readTestrigResources(testrigResourcePrefix, "iptables", iptablesFilenames);
    SortedMap<String, String> routingTablesText =
        readTestrigResources(
            testrigResourcePrefix, BfConsts.RELPATH_ENVIRONMENT_ROUTING_TABLES, rtFilenames);
    Batfish batfish =
        BatfishTestUtils.getBatfishFromTestrigText(
            configurationsText,
            bgpTablesText,
            hostFilesText,
            iptablesFilesText,
            routingTablesText,
            tempFolder);
    return batfish;
  }

  /**
   * Get a new Batfish instance with given configurations, tempFolder should be present for
   * non-empty configurations
   *
   * @param configurationText Map from vendor configuration names to their text
   * @param bgpTablesText Map from hostnames to their bgp table text
   * @param hostText Map from host configuration names to their text
   * @param iptablesText Map from iptables configuration names to their text
   * @param routingTablesText Map from hostnames names to their routing table text
   * @param tempFolder Temporary folder to be used to files required for Batfish
   * @return New Batfish instance
   */
  public static Batfish getBatfishFromTestrigText(
      SortedMap<String, String> configurationText,
      SortedMap<String, String> bgpTablesText,
      SortedMap<String, String> hostText,
      SortedMap<String, String> iptablesText,
      SortedMap<String, String> routingTablesText,
      @Nullable TemporaryFolder tempFolder)
      throws IOException {
    if (!configurationText.isEmpty() && tempFolder == null) {
      throw new BatfishException("tempFolder must be set for non-empty configurations");
    }
    return initBatfishFromTestrigText(
        configurationText, bgpTablesText, hostText, iptablesText, routingTablesText, tempFolder);
  }

  /**
   * Get a new Batfish instance with given configurations, tempFolder should be present for
   * non-empty configurations
   *
   * @param configurations Map of all Configuration Name -> Configuration Object
   * @param tempFolder Temporary folder to be used to files required for Batfish
   * @return New Batfish instance
   */
  public static Batfish getBatfish(
      SortedMap<String, Configuration> configurations, @Nullable TemporaryFolder tempFolder)
      throws IOException {
    if (!configurations.isEmpty() && tempFolder == null) {
      throw new BatfishException("tempFolder must be set for non-empty configurations");
    }
    return initBatfish(configurations, tempFolder);
  }

  private static SortedMap<String, String> readTestrigResources(
      String testrigResourcePrefix, String subfolder, String[] filenames) {
    SortedMap<String, String> content = new TreeMap<>();
    for (String filename : filenames) {
      String path = String.format("%s/%s/%s", testrigResourcePrefix, subfolder, filename);
      String text = CommonUtil.readResource(path);
      content.put(filename, text);
    }
    return content;
  }
}
