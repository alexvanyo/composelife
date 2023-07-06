# wear-baseline-profile-generator

A test module which configures generating a baseline profile for [wear](../wear).

This is a separate module to facilitate only generating a baseline profile when specifically
enabled, by setting the Gradle property `com.alexvanyo.composelife.generateBaselineProfile` to
`true`.

Baseline profiles are automatically generated and committed by CI via
[baseline-profile.yml](../.github/workflows/baseline-profile.yml).
