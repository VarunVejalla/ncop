# GitHub setup

The local repository was initialized on `main`. The research files, ignore
rules, and GitHub Actions workflow are ready. The setup environment permits
source-file edits but blocks writes to `.git`, so no initial commit or remote
has been created. It also lacks `gh` and cannot connect to GitHub.

From a normal terminal in this folder, install GitHub CLI if needed, then run:

```powershell
gh auth login
git add .
git diff --cached --check
git commit -m "Set up asymptotic n-cop research repository"
gh repo create VarunVejalla/ncop --private --source . --remote origin --push
```

The owner name follows the neighboring sorting-network repository. The command
defaults to private visibility for unpublished research; use `--public` instead
if desired. If `VarunVejalla/ncop` already exists, add its URL as `origin` and
push `main` instead of creating another repository.

No license has been selected. Choose one before offering reuse permissions;
the sorting-network project's license was not copied to this different project.
