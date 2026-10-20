/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.«60_8_1_1»
public import ReasLib.CategoryTheory.Limits.FiniteNonempty.Preserves
import Mathlib.Tactic.CrossRefAttribute

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

@[expose] public section

universe u

/-- Lemma 60.8.2 (1): the category `CRIS(X/S)`, represented by
`RelativeCRIS S I γ h_compatible X x₀`, has all finite nonempty limits, and
therefore has pair products and fibre products. -/
@[stacks 07I9]
instance relativeCRIS_hasFiniteNonemptyLimits
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme} :
    HasFiniteNonemptyLimits (RelativeCRIS S I γ h_compatible X x₀) := sorry

/-- Lemma 60.8.2 (2): the functor `crystallineForgetful` representing
(60.8.1.1) preserves all finite nonempty limits. -/
@[stacks 07I9]
instance crystallineForgetful_preservesFiniteNonemptyLimits
    {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    PreservesFiniteNonemptyLimits
      (crystallineForgetful S I γ h_compatible s X x₀ h_p) := sorry
