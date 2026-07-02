# GitHub Discussions Guide

Use GitHub Discussions for Lean questions, formalization proposals, proof attempts, checked support lemmas, counterexamples, independent builds, and mapping between informal WCT claims and precise formal statements.

## Recommended categories

- **Announcements**: Releases, toolchain changes, newly checked theorems, and changes in formal status.
- **General**: Broad conversation about formalization architecture and priorities.
- **Q&A**: Focused Lean or mathematical questions with exact references and minimal examples.
- **Ideas**: Proposed theorem statements, definitions, proof plans, and counterexample searches.
- **Show and tell**: Checked results, failed proofs, independent builds, refactors, and claim mappings.

## Formal-status language

- **Checked**: Lean accepts the exact theorem under the encoded definitions, imports, and assumptions.
- **Disproved**: A valid counterexample or contradiction rejects the proposed statement.
- **Blocked**: The statement may be meaningful, but a required lemma, definition, or library result is missing.
- **Incomplete**: The proof contains placeholders, admitted steps, unresolved goals, or unavailable dependencies.
- **Informal only**: A prose claim has not yet been translated into a precise theorem statement.

A checked support lemma does not automatically establish the broader physical claim that motivated it. Discussions should identify the exact formal statement, encoded assumptions, dependency chain, and the gap between the theorem and any informal interpretation.

## Minimum standard for formal results

Include the repository commit, Lean and Lake versions, mathlib or dependency revision, exact build command, theorem signature, imports, definitions, all assumptions, proof status, build output, and links to the proof file or pull request. Failed proof attempts and counterexamples should be preserved rather than hidden.

Use issues for bounded implementation tasks. Keep theorem design, proof strategy, mathematical interpretation, and the consequences of success or failure in Discussions.
