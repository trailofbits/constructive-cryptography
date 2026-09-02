# Historical humanity audit

This document records the diagnosis that led to the semantic-backend redesign.
Current architecture, status, and acceptance criteria live in
[`SPEC.md`](SPEC.md); this file must not be used as a second status document.

The original preview exposed three independent problems:

1. its selected root was a generic H-coefficient example rather than a genuine
   query-restricted URF/URP security theorem;
2. direct `Expr -> String` handlers and tactic describers had no typed message
   layer or cryptographic proof planner; and
3. several polished sentences were selected by local names (`Bad`, `h_real`,
   `h_ideal`) or theorem-specific tactic substrings.

Consequently, manually improving that preview's paragraph is not a fix.  The
replacement must classify checked declarations and theorem applications into
typed semantic roles, build a domain proof plan, and only then realize prose.
It must also pass alpha-renaming, proof-refactoring, negative-classification,
root-content, evidence, and corpus-language tests.

The visually inspected file `preview/switching.html` remains a development
fixture until it passes the first vertical-slice definition of done in
`SPEC.md`.
