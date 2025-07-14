# Memory Bootstrapping

[`gemini-cli`][gemini-cli] allows configuring instructional context by specifying `GEMINI.md` files
throughout the project in a hierarchical manner. This
["hierarchical instructional context"][hierarchical-instructional-context] is also referred
to as "memory".

This memory is appended at the end of the system prompt, and allows a direct way to customize
`gemini-cli`'s behavior in the project.

To initially create the set of `GEMINI.md` files for this project, I'm using `gemini-cli` itself
to generate them, using a process I'm terming "memory bootstrapping" to initially generate and
refine the `GEMINI.md` files. This is a collaborative and iterative process - as `gemini-cli` makes
changes, I make corrections and tweaks, and I continuously refresh the memory in `gemini-cli`
(with `/memory refresh`) to update the project structure.

The starting prompt I using with `gemini-cli` is the following, which includes the direct
documentation of what `GEMINI.md` files do from the `gemini-cli` documentation:

## Prompt to `gemini-cli`:

Help me create `GEMINI.md` files and update existing `GEMINI.md` files for this project.
At the end of these instructions I'll include the documentation for what `GEMINI.md` files do,
per the documentation for `gemini-cli`.
I want to iteratively create and update files to "memory bootstrap" this project for `gemini-cli`,
so that additional usage of `gemini-cli` is more tailored to this project.
As `GEMINI.md` files are created, I will make adjustments as needed then reload memory regularly.
If something should be added but isn't knowable from the project context, don't make assumptions -
instead, leave a clear TODO in the `GEMINI.md` file for me to fill in.
Prioritize looking for existing markdown files and link to them as appropriate for project structure
documentation.

Here is the documentation for what `GEMINI.md` files do:

## Hierarchical Instructional Context

While not strictly configuration for the CLI's _behavior_, context files (defaulting to `GEMINI.md` but configurable via the `contextFileName` setting) are crucial for configuring the _instructional context_ (also referred to as "memory") provided to the Gemini model. This powerful feature allows you to give project-specific instructions, coding style guides, or any relevant background information to the AI, making its responses more tailored and accurate to your needs. The CLI includes UI elements, such as an indicator in the footer showing the number of loaded context files, to keep you informed about the active context.

- **Purpose:** These Markdown files contain instructions, guidelines, or context that you want the Gemini model to be aware of during your interactions. The system is designed to manage this instructional context hierarchically.

### Example Context File Content (e.g., `GEMINI.md`)

Here's a conceptual example of what a context file at the root of a TypeScript project might contain:

````markdown
# Project: My Awesome TypeScript Library

## General Instructions:

- When generating new TypeScript code, please follow the existing coding style.
- Ensure all new functions and classes have JSDoc comments.
- Prefer functional programming paradigms where appropriate.
- All code should be compatible with TypeScript 5.0 and Node.js 20+.

## Coding Style:

- Use 2 spaces for indentation.
- Interface names should be prefixed with `I` (e.g., `IUserService`).
- Private class members should be prefixed with an underscore (`_`).
- Always use strict equality (`===` and `!==`).

## Specific Component: `src/api/client.ts`

- This file handles all outbound API requests.
- When adding new API call functions, ensure they include robust error handling and logging.
- Use the existing `fetchWithRetry` utility for all GET requests.

## Regarding Dependencies:

- Avoid introducing new external dependencies unless absolutely necessary.
- If a new dependency is required, please state the reason.
````

This example demonstrates how you can provide general project context, specific coding conventions, and even notes about particular files or components. The more relevant and precise your context files are, the better the AI can assist you. Project-specific context files are highly encouraged to establish conventions and context.

- **Hierarchical Loading and Precedence:** The CLI implements a sophisticated hierarchical memory system by loading context files (e.g., `GEMINI.md`) from several locations. Content from files lower in this list (more specific) typically overrides or supplements content from files higher up (more general). The exact concatenation order and final context can be inspected using the `/memory show` command. The typical loading order is:
    1.  **Global Context File:**
        - Location: `~/.gemini/<contextFileName>` (e.g., `~/.gemini/GEMINI.md` in your user home directory).
        - Scope: Provides default instructions for all your projects.
    2.  **Project Root & Ancestors Context Files:**
        - Location: The CLI searches for the configured context file in the current working directory and then in each parent directory up to either the project root (identified by a `.git` folder) or your home directory.
        - Scope: Provides context relevant to the entire project or a significant portion of it.
    3.  **Sub-directory Context Files (Contextual/Local):**
        - Location: The CLI also scans for the configured context file in subdirectories _below_ the current working directory (respecting common ignore patterns like `node_modules`, `.git`, etc.).
        - Scope: Allows for highly specific instructions relevant to a particular component, module, or subsection of your project.
- **Concatenation & UI Indication:** The contents of all found context files are concatenated (with separators indicating their origin and path) and provided as part of the system prompt to the Gemini model. The CLI footer displays the count of loaded context files, giving you a quick visual cue about the active instructional context.
- **Commands for Memory Management:**
    - Use `/memory refresh` to force a re-scan and reload of all context files from all configured locations. This updates the AI's instructional context.
    - Use `/memory show` to display the combined instructional context currently loaded, allowing you to verify the hierarchy and content being used by the AI.
    - See the [Commands documentation](./commands.md#memory) for full details on the `/memory` command and its sub-commands (`show` and `refresh`).

By understanding and utilizing these configuration layers and the hierarchical nature of context files, you can effectively manage the AI's memory and tailor the Gemini CLI's responses to your specific needs and projects.

[//]: # (website links)
[gemini-cli]: https://github.com/google-gemini/gemini-cli
[hierarchical-instructional-context]: https://github.com/google-gemini/gemini-cli/blob/main/docs/cli/configuration.md#context-files-hierarchical-instructional-context
