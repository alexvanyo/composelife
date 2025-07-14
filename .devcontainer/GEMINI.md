# Directory: .devcontainer

This directory contains the configuration for a [Dev Container](https://containers.dev/), which allows for a consistent and reproducible development environment.

## Purpose & Contents

- **`devcontainer.json`**: This is the main configuration file.
  - It specifies the base Docker image to use for the development environment (`mcr.microsoft.com/devcontainers/universal:3`).
  - It includes the `nordcominc/devcontainer-features/android-sdk` feature, which automatically installs the Android SDK within the container.
- This setup is designed to simplify environment setup for new contributors, ensuring all necessary dependencies (like the correct Android SDK) are available without manual installation on the host machine.
