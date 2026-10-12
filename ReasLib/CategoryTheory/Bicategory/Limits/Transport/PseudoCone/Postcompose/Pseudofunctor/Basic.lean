/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Hom

/-!
# The pseudofunctor postcomposing conical pseudocones

A strong transformation between pseudodiagrams acts on their conical pseudocones by
postcomposition. This file assembles the object, `1`-morphism, and `2`-morphism actions
and their identity and composition comparisons into a pseudofunctor.

The bicategorical coherence witnesses remain private implementation details. Projection
and component formulas belong in a separate computations module.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uB vB wB uJ vJ wJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoCone

variable {J : Type uJ} [Bicategory.{wJ, vJ} J]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {E F : Pseudofunctor J B}

/-- Postcomposition by a strong transformation of pseudodiagrams is a pseudofunctor
between their bicategories of conical pseudocones.

It retains apex objects, apex maps, and apex `2`-morphisms literally. Its identity and
composition comparisons are the canonical `ColaxCostructuredArrow` comparison fields. -/
abbrev postcompose
    (α : Pseudofunctor.StrongTrans E F) :
    Pseudofunctor (PseudoCone E) (PseudoCone F) :=
  ColaxCostructuredArrow.postcompose (Pseudofunctor.constDiagram J B) α

/- Data and axiom audit (mathlib 4.32):

`postcompose` is the transparent conical-pseudocone specialization of the canonical
`ColaxCostructuredArrow.postcompose`. Its object, morphism, cell, comparison, and coherence
fields therefore have a single owner; this file adds no deferred proof or bundled data. -/

end Bicategory.PseudoCone

end CategoryTheory
