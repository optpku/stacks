/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Degreewise split short exact triangles in the derived category

This file separates the canonical change-of-functor comparison from the
noncanonical uniqueness-up-to-isomorphism statement for distinguished
triangles.  Only the former is exposed as concrete `Iso` data.
-/

open CategoryTheory
open CategoryTheory.Pretriangulated
open ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.ShortExact

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- The canonical comparison between first passing a degreewise split triangle
to the homotopy category and then applying `Qh`, and applying `Q` directly. -/
@[stacks 0154]
noncomputable def degreewiseSplitImageIso
    {S : ShortComplex (CochainComplex 𝒜 ℤ)}
    (σ : ∀ n, (S.map (HomologicalComplex.eval 𝒜 (up ℤ) n)).Splitting) :
    _root_.DerivedCategory.Qh.mapTriangle.obj
        (CochainComplex.trianglehOfDegreewiseSplit S σ) ≅
      _root_.DerivedCategory.Q.mapTriangle.obj
        (CochainComplex.triangleOfDegreewiseSplit S σ) :=
  (Functor.mapTriangleCompIso
      (HomotopyCategory.quotient 𝒜 (up ℤ)) _root_.DerivedCategory.Qh).symm.app _ ≪≫
    (Functor.mapTriangleIso (_root_.DerivedCategory.quotientCompQhIso 𝒜)).app _

/-- The image in the derived category of a degreewise split homotopy triangle
is distinguished. -/
@[stacks 0154]
theorem degreewiseSplitImage_distinguished
    {S : ShortComplex (CochainComplex 𝒜 ℤ)}
    (σ : ∀ n, (S.map (HomologicalComplex.eval 𝒜 (up ℤ) n)).Splitting) :
    _root_.DerivedCategory.Qh.mapTriangle.obj
        (CochainComplex.trianglehOfDegreewiseSplit S σ) ∈
      distTriang (_root_.DerivedCategory 𝒜) := sorry

/-- Lemma 13.12.3 (`0154`): the derived triangle of a degreewise split short
exact sequence is isomorphic to the image of its canonical homotopy triangle. -/
@[stacks 0154]
theorem triangle_isomorphic_degreewiseSplitImage
    {S : ShortComplex (CochainComplex 𝒜 ℤ)}
    (σ : ∀ n, (S.map (HomologicalComplex.eval 𝒜 (up ℤ) n)).Splitting) :
    IsIsomorphic
      (_root_.DerivedCategory.triangleOfSES
        (HomologicalComplex.shortExact_of_degreewise_shortExact S fun n =>
          (σ n).shortExact))
      (_root_.DerivedCategory.Qh.mapTriangle.obj
        (CochainComplex.trianglehOfDegreewiseSplit S σ)) := sorry

end CategoryTheory.DerivedCategory.ShortExact
