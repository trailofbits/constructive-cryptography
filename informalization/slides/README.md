# Swiss Crypto Day 2026 deck

This nested Verso/reveal.js project is the presentation surface for the
informalization project. It owns slide selection, pacing, speaker notes, and
the ToB/TikZ visual language. It does not import or duplicate the CBC proof.

The complete hand-authoring cheat sheet is the repository-level
[`SLIDES.md`](../SLIDES.md). It covers standard Verso syntax and every custom
surface used by this deck.

The proof slide is a native Verso block. It embeds
`../preview/cbc-mac.document.json` and mounts it with the same renderer and
stylesheet used by the standalone reader. A direct deck build consumes the
existing generated document and is useful for visual work:

```sh
cd slides
lake exe swiss-crypto-day
python3 -m http.server 8000 --directory _draft_talk
```

Open <http://127.0.0.1:8000>. The generated deck is self-contained apart from
its ordinary Verso assets; there is no nested page or iframe.

For an automatically rebuilding development session, run from the parent
project:

```sh
./scripts/watch-swiss-crypto-day.sh --serve --port 8766
```

The browser reloads only after a successful build. A change confined to this
deck recompiles only Verso; changes to the live theorem, its upstream library,
the informalizer, or the shared reader regenerate both the proof document and
the deck.

For a presentation build, first regenerate the reader from the completed live
CBC theorem using the command documented in the parent README. Generation is
fail-closed: an incomplete downstream proof is not replaced by slide-authored
evidence.
