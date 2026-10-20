/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy.NormalizedMoore
import StacksCheckRecall

/-!
@stack 019S

# Source-facing recall for Lemma 14.27.1

The reusable transport of simplicial homotopies to alternating-face and
normalized-Moore chain complexes is owned by the corresponding neutral
`ReasLib` support leaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicTopology
open AlgebraicTopology.DoldKan

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

section AlternatingFace

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasFiniteBiproducts A]
variable {U V : SimplicialObject A} (a b : U ⟶ V) (h : Homotopic a b)

/- Lemma 14.27.1 (1): zigzag-homotopic simplicial morphisms induce homotopic maps on
alternating-face chain complexes. -/
@[stacks 019S "Lemma 14.27.1 (1)"]
#check (h.alternatingFace :
  homotopic A (ComplexShape.down ℕ)
    ((alternatingFaceMapComplex A).map a)
    ((alternatingFaceMapComplex A).map b))

end AlternatingFace

section NormalizedMoore

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : SimplicialObject A} (a b : U ⟶ V) (h : Homotopic a b)

/- Lemma 14.27.1 (2): zigzag-homotopic simplicial morphisms induce homotopic maps on
normalized Moore chain complexes. -/
@[stacks 019S "Lemma 14.27.1 (2)"]
#check (h.normalizedMoore :
  homotopic A (ComplexShape.down ℕ)
    ((normalizedMooreComplex A).map a)
    ((normalizedMooreComplex A).map b))

end NormalizedMoore

end CategoryTheory.SimplicialObject
