# Build Paper I in Visual Studio Code on Windows

1. Install Visual Studio Code and Git for Windows. In VS Code, open **Extensions** with **Ctrl+Shift+X**. Install **Lean 4** from the publisher **leanprover**. Complete the extension's setup, including Elan, and reopen VS Code. [Official Lean installation guide](https://lean-lang.org/install/)
2. Right-click the ZIP in File Explorer and choose **Extract All**. Use a short local path such as `C:\Lean`. In VS Code, select **File → Open Folder** and open the extracted **Paper_I_Lean** folder. The files `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` are directly inside it.
3. Select **Terminal → New Terminal**. In the PowerShell terminal, run these commands one at a time.

   ```powershell
   git --version
   lake env lean --version
   lake exe cache get
   lake build
   $LASTEXITCODE
   ```

4. Check that Lean reports version **4.34.0**. The first build downloads dependencies and may take a while. A successful build ends with **Build completed successfully** and the last line prints **0**. Warnings about `sorry` correspond to the original literature inputs listed in [ASSUMPTIONS.md](ASSUMPTIONS.md).
5. Run the following command from the same directory to inspect the dependencies of individual theorems. For each result, `sorryAx` means that it uses at least one admitted proof.

   ```powershell
   lake env lean RevisedPaperIAxiomReport.lean
   ```

6. To read a proof interactively, open its `.lean` file and click inside the proof. Use **Lean: Toggle Infoview** from **Ctrl+Shift+P** to see the goal and hypotheses at the cursor.

If PowerShell cannot find `lake`, complete the Elan setup and reopen VS Code. If you see an unknown-module error, check that the terminal is in the folder containing `lakefile.toml`, then run the cache and build commands in order. The manifest pins the dependencies for this project.
