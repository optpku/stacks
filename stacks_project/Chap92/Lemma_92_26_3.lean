/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap92.Lemma_92_26_3_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison of cotangent complexes of algebraic spaces with representing schemes

Lemma 92.26.3 identifies `L_{X/Y}` with `ε* L_{X0/Y0}` in `D(𝒪_X)` when `X` and `Y`
are represented by schemes `X0` and `Y0`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory

noncomputable section

universe u

/-- Lemma 92.26.3. Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Assume `X` and `Y` representable by schemes `X0` and `Y0`. Then there
is a canonical identification `L_{X/Y} = ε* L_{X0/Y0}` in
`DerivedCategory (CommModules (ofOver X0))` where `ε` is as in Derived Categories of
Spaces, Section 75.4 and `L_{X0/Y0}` is as in Definition 92.24.1. -/
@[stacks 08VF]
abbrev epsilonStarSchemeCompareIso {S : Scheme.{u}} {X0 Y0 : Over S}
    (f0 : X0 ⟶ Y0) :
    Cotangent.epsilonStarSchemeCotangent f0 ≅ Cotangent.cotangent (ofOverMap f0) :=
  Cotangent.epsilonStarSchemeCompareIso f0

/-- The forward map of `epsilonStarSchemeCompareIso` is `epsilonStarSchemeCompare`. -/
theorem epsilonStarSchemeCompareIso_hom {S : Scheme.{u}} {X0 Y0 : Over S}
    (f0 : X0 ⟶ Y0) :
    (epsilonStarSchemeCompareIso f0).hom = Cotangent.epsilonStarSchemeCompare f0 :=
  sorry
