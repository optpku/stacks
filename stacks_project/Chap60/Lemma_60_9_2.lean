/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap60.Lemma_60_9_2_Inclusion
public import stacks_project.Chap60.Lemma_60_9_2_Topos

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open scoped MorphismOfTopoiIn

universe u

variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
variable (p : ℕ) [Fact (Nat.Prime p)]
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- Lemma 60.9.2 (1): the inclusion functor `Cris(X/S) ⥤ CRIS(X/S)`. -/
@[stacks 07IJ]
abbrev smallCrystallineInclusion_source :=
  smallCrystallineInclusion S I γ h_compatible X x₀

/-- Lemma 60.9.2 (2): the inclusion `Cris(X/S) ⥤ CRIS(X/S)` preserves finite nonempty limits. -/
@[stacks 07IJ]
theorem smallCrystallineInclusion_preservesFiniteNonemptyLimits_source :
    PreservesFiniteNonemptyLimits
      (smallCrystallineInclusion S I γ h_compatible X x₀) := sorry

/-- Lemma 60.9.2 (3): the inclusion `Cris(X/S) ⥤ CRIS(X/S)` is fully faithful. -/
@[stacks 07IJ]
def smallCrystallineInclusion_fullyFaithful_source :
    (smallCrystallineInclusion S I γ h_compatible X x₀).FullyFaithful :=
  smallCrystallineInclusion_fullyFaithful S I γ h_compatible X x₀

/-- Lemma 60.9.2 (4): the inclusion is continuous for the Zariski crystalline topologies. -/
@[stacks 07IJ]
theorem smallCrystallineInclusion_isContinuous_source :
    Functor.IsContinuous
      (smallCrystallineInclusion S I γ h_compatible X x₀)
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (crystallineZariskiTopology S I γ h_compatible X x₀) := sorry

/-- Lemma 60.9.2 (5): the inclusion is cocontinuous for the Zariski crystalline topologies. -/
@[stacks 07IJ]
theorem smallCrystallineInclusion_isCocontinuous_source :
    Functor.IsCocontinuous
      (smallCrystallineInclusion S I γ h_compatible X x₀)
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (crystallineZariskiTopology S I γ h_compatible X x₀) := sorry

/-- Lemma 60.9.2 (6): the inclusion induces `i : (X/S)_cris ⟶ (X/S)_CRIS`. -/
@[stacks 07IJ]
noncomputable abbrev smallToBigCrystallineToposMorphism_source
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasPointwiseRightKanExtension P]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))] :=
  smallToBigCrystallineToposMorphism S I γ h_compatible X x₀ p s h_p

/-- Lemma 60.9.2 (7): there is `π : (X/S)_CRIS ⟶ (X/S)_cris` with `π⁻¹ = i_!`. -/
@[stacks 07IJ]
noncomputable abbrev bigToSmallCrystallineToposMorphism_source
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P] :=
  bigToSmallCrystallineToposMorphism S I γ h_compatible X x₀ p s h_p

/-- Lemma 60.9.2 (8): the composite `π ∘ i` is the identity on `(X/S)_cris`. -/
@[stacks 07IJ]
theorem bigToSmallCrystallineToposMorphism_comp_smallToBig_source
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasPointwiseRightKanExtension P]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P] :
    MorphismOfTopoiIn.comp
        (bigToSmallCrystallineToposMorphism S I γ h_compatible X x₀ p s h_p)
        (smallToBigCrystallineToposMorphism S I γ h_compatible X x₀ p s h_p) =
      MorphismOfTopoiIn.id
        (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) := sorry

/-- Lemma 60.9.2 (9): `π_* = i⁻¹`. -/
@[stacks 07IJ]
theorem bigToSmallCrystallineToposMorphism_pushforward_eq_inverseImage_source
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasPointwiseRightKanExtension P]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))]
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P] :
    (bigToSmallCrystallineToposMorphism S I γ h_compatible X x₀ p s h_p).pushforward =
      (smallToBigCrystallineToposMorphism S I γ h_compatible X x₀ p s h_p).inverseImage := sorry
