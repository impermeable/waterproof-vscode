import { Version, VersionRequirement } from "../../src/version-checker/version";

describe("VersionRequirement >= (versionGreaterThan)", () => {
  it.each([
    // [requirement, installed, satisfied]
    [">=3.1.1", "3.1.1", true],
    [">=3.1.1", "3.1.2", true],
    [">=3.1.1", "3.1.0", false], // patch too low
    [">=3.1.1", "3.0.9", false],
    [">=3.1.1", "2.9.9", false],
    [">=3.1.1", "3.2.0", true], // higher minor, lower patch
    [">=3.1.1", "4.0.0", true], // higher major, lower minor and patch
    [">=0.2.5", "0.2.4", false],
    [">=0.2.5", "0.10.0", true], // numeric, not lexicographic
    [">=3.1", "3.1.0", true], // unspecified patch in requirement
    [">=3.1", "3.0.9", false],
    [">=3", "3.0.0", true],
    [">=3.1.1", "3.1", false], // unspecified patch in installed counts as 0
    [">=3.1.0", "3.1", true],
  ])("%s with %s installed -> %s", (requirement, installed, satisfied) => {
    const req = VersionRequirement.fromString(requirement);
    expect(req.isSatisfiedBy(Version.fromString(installed))).toBe(satisfied);
  });
});
