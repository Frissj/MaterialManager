Tired of setting up materials across blend files? Wish you had a centralized, intelligent material library that just works? Introducing the MaterialList Manager & Persistent Library addon for Blender!

Built to help you cram as many materials into your scene as possible to make the environments varied and complex! 
Key Features:

✨ Unified & Persistent Material Library

    Central Hub: Automatically merges your local project materials (non-"mat_" prefixed by display name) into a persistent, central material_library.blend. Access and reuse your curated materials across all your projects effortlessly!
    Smart Content-Based Updates: New and modified materials are intelligently added or updated in the central library.
    Pack library textures into the blend file so you can share materials with others on your project! 
    Smart Library Trimming: Keep your library lean and relevant by optionally trimming it to the 100 most recently used materials.

⚙️ Advanced In-Project Material Management

    Enhanced Material List: View all project materials—both local and linked from your library—with clear, automatically generated previews directly in the 3D View sidebar.
    UUID & Display Names: Local materials are robustly managed by an internal unique UUID (their Blender datablock name for non-"mat_" prefixed materials), while you interact with user-friendly, editable display names that are stored persistently.
    Asynchronous Thumbnails: Enjoy a blazing-fast, non-blocking UI thanks to asynchronous thumbnail generation. Thumbnails are created by background workers, batched for efficiency, cached, and preloaded.
    Workspace Modes & Backups:
        Editing Mode: Your familiar Blender workspace.
        Reference Mode: Instantly create a combined snapshot of your current visible scene geometry in a dedicated "Reference" collection which you can switch between if you want to keep the games theme!
        Persistent Backups: Automatically back up material assignments for your "Reference" and "Editing" configurations.

🚀 Powerful Tools & Operators at Your Fingertips

    Duplicate & Make Local: Quickly create editable local copies of any material. Convert linked library materials into local versions within your current project, automatically remapping all users.
    Flexible Assignment: Easily assign materials to objects or selected faces, add materials to object slots without immediate assignment, or quickly unassign all "mat_" prefixed utility materials.
    Batch Utilities: "Rename to Albedo" (renames based on Base Color texture), "Select Dominant Material" on your active object, and "Localise All Users" (batch converts library materials to local in all linked project files).
    Intuitive UI: Search, sort (alphabetically/recency), filter (local/used, hide "mat_"), and get detailed previews and information for your selected material.

💪 Robust, Stable & Developer-Friendly

    SQLite Database Backend: All critical metadata—names, content hashes, timestamps, material origins, backups, and more—is stored reliably in a dedicated SQLite database.
    Background Processing: Heavy tasks like library updates, thumbnail generation, and file localisation are offloaded to background processes, keeping Blender responsive.
    Detailed Logging & Error Handling: Designed for stability with comprehensive feedback and graceful error management.
