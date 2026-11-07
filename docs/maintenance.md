# Repository maintenance

<!-- [impl->req~public-foundation~1] -->

The repository is public and MIT licensed. Its
[Project](https://github.com/users/kbak/projects/2) remains private; changing
Project visibility is a separate maintainer decision. Public issues and pull
requests are the contributor-facing planning interface. Launch acceptance is
tracked in the [public-launch settings issue](https://github.com/kbak/clafer-semantics/issues/5).

Maintain these repository controls:

- Main-branch protection must require PRs, a passing `Lean and IntentBond` check on
  an up-to-date branch, and resolved review conversations. Force pushes and branch
  deletion are blocked. Administrators are subject to the same restrictions. For the
  current single-maintainer project, there is no minimum approving-review count:
  GitHub cannot count an author's own approval. Require independent semantic review of IntentBond exit-4 changes
  before merge, and record its disposition in the PR. A green CI check does
  not supply that review. Require one approving review once another reviewer is
  available; dismiss stale approvals and require approval of the latest push.
- GitHub private vulnerability reporting is enabled.
  [SECURITY.md](../SECURITY.md) and the issue chooser direct sensitive reports
  to the private form. Keep their destinations consistent and verify availability
  after any visibility or security-setting change.
- Review tracked files and history for private data; check attribution for any
  imported publication material or upstream code. Include commit messages and
  author metadata, all branches/tags intended for publication, and retained
  change records. Keep redacted findings and source identities in external
  evidence; do not rewrite history or remove frozen records without approval.
- Keep the Project private unless its publication is separately authorized.

GitHub's [branch-protection guidance](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-protected-branches)
and [private-reporting guidance](https://docs.github.com/en/code-security/how-tos/report-and-fix-vulnerabilities/configure-vulnerability-reporting/configure-for-a-repository)
describe feature availability and configuration. CI and contributor instructions
alone do not enforce protected-branch rules; inspect the live settings when
reviewing repository policy.

IntentBond updates must update both `requirements/intentbond.txt` and the pinned
skill link in `AGENTS.md`. Lean updates must update `lean-toolchain` and pass the
shared checks. Review checking-policy changes explicitly; IntentMade's trusted
scope pin must also be deliberately advanced when adopting a new policy.

## Behavioral integration controls

The temporary `behavioral` branch is retired after accepted integration in both
repositories. Structural and behavioral changes now use main's PR, validation and
review controls above. [CI](../.github/workflows/ci.yml) covers PRs targeting any
branch and pushes to `main`, using the manifest-based validation selector. Full
validation remains required for source and tooling changes; documentation checks
do not provide new Lean execution evidence or semantic approval.

The [integration contract](behavioral-profile.md#integration-and-acceptance)
retains the completed two-repository gate obligations and immutable handoff
requirements. Its historical branch controls are not instructions to recreate
`behavioral`. Preserve main's hosted protection when retiring temporary branches;
CI configuration and contributor documentation do not install those controls.
Acceptance records belong in the public issues/PRs and external evidence.

## Maintainer acceptance

<!-- [impl->req~github-tracking~1] -->

A maintainer's merge of a PR completing an issue communicates approval and
acceptance of that change, including its stated scope and assumptions, unless
the maintainer explicitly leaves acceptance pending. A separate acceptance
message or GitHub approving-review submission is not required. On observing the
merge, record the PR and immutable merged SHA, reconcile the delivered acceptance
criteria, close the completed issue with the ticket helper, mark it Done and
refresh affected unstarted tickets in both repositories. Do this as part of the
merge follow-up, including merges into a non-default integration branch.

Keep pre-merge review obligations and validation evidence intact. A historical
IntentBond exit-4 result describes automation at the time of checking; it does
not override subsequent maintainer acceptance. Record that acceptance separately
without changing the evidence or claiming an independent review was performed
when none is recorded. Do not keep completed work open solely because the PR
description still says review pending; reconcile that description too.

A PR closed without merging, successful CI alone, or a merge that leaves some
acceptance criteria undelivered does not complete the issue. Record any remaining
work explicitly. Research releases retain their own review and publication gates.

## Research snapshots

[CITATION.cff](../CITATION.cff) identifies the software; cite the exact commit used
and the SoSyM paper separately. A package version in `lakefile.toml` alone does
not designate a reviewed release. Research snapshot tags identify reproducible
source without promising API stability or supported releases.

Before tagging a snapshot, select a commit on main with passing CI and retained
IntentBond evidence matched to that commit. Have an independent reviewer record
the source revision, inspected declarations, findings and disposition in the PR.
Use this focused checklist:

- Compare the five [accepted paper corrections](sosym-errata.md) with their source
  passages and actual counterexamples/proofs; distinguish corrections from choices.
- Inspect the [telematics source-to-core inventory](telematics.md), final selections
  and all twelve bodies. Confirm manual elaboration and the infinite integer
  extent are explicit, and that the final theorem discharges its hypotheses.
- Inspect the assumptions of [constraint preservation](constraint-preservation.md)
  and [finite verification](structural-checker.md); check that public summaries
  do not turn selected or conditional results into unrestricted correctness claims.

Automation and an author's self-review do not supply this independent disposition.
Resolve material findings before publishing. Then create an annotated
`research-YYYY-MM-DD` tag on that reviewed commit, with the commit identity,
review link and evidence reference in the annotation or accompanying release notes.
Retain evidence beyond CI artifact expiry in an external archive. Any software DOI
must identify that software archive, not reuse the paper DOI. Keep review records,
execution reports and snapshot announcements out of living mathematical docs.
