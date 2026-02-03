package org.batfish.dataplane.ibdp;

import static org.batfish.dataplane.ibdp.schedule.IbdpSchedule.Schedule.NODE_COLORED;
import static org.batfish.dataplane.ibdp.schedule.NodeColoredSchedule.Coloring.SATURATION;

import org.apache.commons.configuration2.Configuration;
import org.apache.commons.configuration2.ConfigurationUtils;
import org.apache.commons.configuration2.ImmutableConfiguration;
import org.apache.commons.configuration2.PropertiesConfiguration;
import org.batfish.dataplane.ibdp.schedule.IbdpSchedule.Schedule;
import org.batfish.dataplane.ibdp.schedule.NodeColoredSchedule;
import org.batfish.dataplane.ibdp.schedule.NodeColoredSchedule.Coloring;

/** Settings for {@link IncrementalDataPlanePlugin} */
public final class IncrementalDataPlaneSettings {

  private Configuration _config;

  public static final String PROP_COLORING = "coloring";
  public static final String PROP_SCHEDULE = "schedule";
  /** When true, run BGP sub-iterations until convergence within each routing round (instant withdrawal propagation along chains). */
  public static final String PROP_BGP_CONVERGE_WITHIN_ROUND = "bgpConvergeWithinRound";

  /**
   * Return the underlying configuration (it will be mutable).
   *
   * @return a {@link Configuration}
   */
  public Configuration getConfig() {
    return _config;
  }

  /** Create new settings object and initialize it with defaults */
  public IncrementalDataPlaneSettings() {
    _config = new PropertiesConfiguration();
    initDefaults();
  }

  /**
   * Create new settings, initialize with defaults, but also copy over settings from {@code
   * configSource}
   *
   * @param configSource the configuration options to override the defaults
   */
  public IncrementalDataPlaneSettings(ImmutableConfiguration configSource) {
    this();
    ConfigurationUtils.copy(configSource, _config);
  }

  /** Initialize defaults for all properties */
  private void initDefaults() {
    _config.setProperty(PROP_COLORING, SATURATION.toString());
    _config.setProperty(PROP_SCHEDULE, NODE_COLORED.toString());
    _config.setProperty(PROP_BGP_CONVERGE_WITHIN_ROUND, false);
  }

  /** Return the dataplane computation {@link Schedule} */
  public Schedule getScheduleName() {
    return Schedule.valueOf(_config.getString(PROP_SCHEDULE));
  }

  /**
   * If the schedule is of type {@link NodeColoredSchedule}, get the type of {@link Coloring} to
   * perform
   */
  public Coloring getColoringType() {
    return Coloring.valueOf(_config.getString(PROP_COLORING));
  }

  /**
   * When true, run multiple BGP sub-iterations within each routing round until BGP converges, so
   * that withdrawals propagate along chains (e.g. A -&gt; B -&gt; C) in one round instead of one
   * hop per round.
   */
  public boolean getBgpConvergeWithinRound() {
    return _config.getBoolean(PROP_BGP_CONVERGE_WITHIN_ROUND, false);
  }
}
