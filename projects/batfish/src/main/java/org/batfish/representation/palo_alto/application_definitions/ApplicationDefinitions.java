package org.batfish.representation.palo_alto.application_definitions;

import static org.batfish.common.util.Resources.readResource;

import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.core.type.TypeReference;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import java.nio.charset.StandardCharsets;
import java.util.List;
import java.util.Map;
import org.batfish.common.util.BatfishObjectMapper;

/** Helper class that stores all built-in application definitions for a Palo Alto device. */
public final class ApplicationDefinitions {
  public static ApplicationDefinitions INSTANCE = new ApplicationDefinitions();

  public Map<String, ApplicationDefinition> getApplications() {
    return _applications;
  }

  private ApplicationDefinitions() {
    List<ApplicationDefinition> apps;
    try {
      apps =
          BatfishObjectMapper.ignoreUnknownMapper()
              .readValue(
                  readResource(APPLICATION_DEFINITIONS_PATH, StandardCharsets.UTF_8),
                  new TypeReference<List<ApplicationDefinition>>() {});
    } catch (JsonProcessingException e) {
      apps = ImmutableList.of();
    }
    _applications =
        apps.stream().collect(ImmutableMap.toImmutableMap(ApplicationDefinition::getName, a -> a));
  }

  private final Map<String, ApplicationDefinition> _applications;

  private static final String APPLICATION_DEFINITIONS_PATH =
      "org/batfish/representation/palo_alto/application_definitions/application_definitions.json";
}
