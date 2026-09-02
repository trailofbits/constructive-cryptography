import LanguageDesign.Basic

/-!
# Executable theorem-presentation contract

This module is the shared, proof-independent contract for reader-facing
theorem titles, introductions, and inspectable mathematical references.
Verbose and Informalization may produce different prose, but both must attach
presentation choices to a checked theorem binder or declaration rather than
to an ungrounded display string.
-/

namespace CryptoLanguage.LanguageDesign.Presentation

open Lean

/-- The checked source of a reader-facing mathematical reference. -/
inductive ReferenceTarget where
  | theoremBinder (name : Name)
  | declaration (name : Name)
  deriving Inhabited, BEq, Repr

/-- One displayed mathematical expression and its reader-facing description. -/
structure Reference where
  target : ReferenceTarget
  latex : String
  /-- Atomic notation matched inside larger generated formulas.  When empty,
  `latex` itself is used.  This is presentation identity, not hover prose: the
  hover payload is recovered from Lean at generation time. -/
  hoverLatex : String := ""
  description : String
  deriving Inhabited, BEq, Repr

/-- Typed content from which a theorem introduction is assembled. -/
inductive Fragment where
  | text (value : String)
  | reference (value : Reference)
  deriving Inhabited, BEq, Repr

/-- One paragraph in the theorem introduction. -/
structure Paragraph where
  fragments : Array Fragment := #[]
  deriving Inhabited, BEq, Repr

/-- Author/profile-supplied theorem title and introductions.  The formal
conclusion is deliberately absent: it must be compiled from the checked
theorem statement. -/
structure TheoremPresentation where
  declaration : Name
  title : String
  introductions : Array Paragraph := #[]
  deriving Inhabited, BEq, Repr

def Reference.isWellFormed (reference : Reference) : Bool :=
  !reference.latex.trimAscii.isEmpty &&
    !reference.description.trimAscii.isEmpty

def Paragraph.isWellFormed (paragraph : Paragraph) : Bool :=
  !paragraph.fragments.isEmpty && paragraph.fragments.all fun fragment =>
    match fragment with
    | .text value => !value.isEmpty
    | .reference reference => reference.isWellFormed

def TheoremPresentation.isWellFormed
    (presentation : TheoremPresentation) : Bool :=
  !presentation.declaration.isAnonymous &&
    !presentation.title.trimAscii.isEmpty &&
    !presentation.introductions.isEmpty &&
    presentation.introductions.all Paragraph.isWellFormed

end CryptoLanguage.LanguageDesign.Presentation
