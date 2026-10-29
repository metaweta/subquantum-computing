# Publish This Repository to GitHub

The GitHub account connected during preparation was `metaweta`.

## Recommended first publication

Create a **private**, empty GitHub repository named `subquantum-computing`. Do not initialize it with a README, license, or `.gitignore`, because those files are already present here.

Then run from this directory:

```bash
git remote add origin git@github.com:metaweta/subquantum-computing.git
git push -u origin main --tags
```

For HTTPS instead of SSH:

```bash
git remote add origin https://github.com/metaweta/subquantum-computing.git
git push -u origin main --tags
```

If you choose another repository name, replace the URL accordingly.

## Open in Codex

After pushing, connect or select the GitHub repository in Codex. Codex should read `AGENTS.md` before making changes. The repository contains the durable context needed for future work; Codex does not need access to the original ChatGPT conversation.
