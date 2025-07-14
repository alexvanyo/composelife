# Directory: keystore

This directory contains keystore files for signing the application.

## Purpose & Contents

- **`debug.jks`**: This is the Java KeyStore (JKS) file containing the signing key for the **debug** builds of the Android application. This is a standard practice in Android development to allow apps to be installed and run on devices during development.

**Note:** This keystore is for debug purposes only and should not contain production signing keys. Production keys should be stored securely and not checked into version control.
