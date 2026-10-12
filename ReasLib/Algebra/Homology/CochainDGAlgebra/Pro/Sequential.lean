/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Pro.Sequential.Presentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sequential pro-objects of cochain differential graded algebras

This leaf specializes the reusable sequential pro-object interface to cochain DGAs.  It owns
the represented pro-DGA, while adjacent transitions continue to use the canonical
`SequentialInverseSystem.stepMap` API.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Opposite

namespace CochainDGAlgebra.InverseSystem

variable {R : Type u} [CommRing R]

/-- The pro-object represented by a sequential inverse system of cochain DGAs. -/
@[stacks 0GZG "inverse systems of differential graded algebras as pro-objects"]
noncomputable abbrev proObject
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, v} R)) :
    CategoryTheory.Pro (CochainDGAlgebra.{u, v} R) :=
  (CategoryTheory.Pro.lim (C := CochainDGAlgebra.{u, v} R) ℕᵒᵖ).obj A

end CochainDGAlgebra.InverseSystem
