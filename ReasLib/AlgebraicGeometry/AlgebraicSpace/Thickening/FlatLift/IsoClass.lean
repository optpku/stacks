/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Torsor.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.Translation

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension
open AlgebraicGeometry.AlgebraicSpace.Thickening
open scoped AlgebraicGeometry.AlgebraicSpace DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening
namespace FlatLift

variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}
variable {t : Y ⟶ Y'} [IsFirstOrderThickening t] {f : X ⟶ Y} [Flat f]

/-- The setoid identifying flat lifts that admit an ambient isomorphism over `Y'`
reducing to the identity on `X`. -/
def isoSetoid (t : Y ⟶ Y') [IsFirstOrderThickening t] (f : X ⟶ Y) [Flat f] :
    Setoid (FlatLift t f) where
  r L₁ L₂ := Nonempty (Hom L₁ L₂)
  iseqv := sorry

/-- Two flat lifts are related iff they admit a morphism of lifts. -/
theorem isoSetoid_rel (L₁ L₂ : FlatLift t f) :
    isoSetoid t f L₁ L₂ ↔ Nonempty (Hom L₁ L₂) := sorry

/-- Isomorphism classes of flat first-order lifts of `f` across `t`. -/
abbrev IsoClass (t : Y ⟶ Y') [IsFirstOrderThickening t] (f : X ⟶ Y) [Flat f] :=
  Quotient (isoSetoid t f)

/-- The isomorphism class of a given flat lift. -/
def isoClassMk (L : FlatLift t f) : IsoClass t f :=
  Quotient.mk (isoSetoid t f) L

/-- A morphism of flat lifts identifies isomorphism classes. -/
theorem isoClassMk_eq_mk_of_hom {L₁ L₂ : FlatLift t f} (φ : Hom L₁ L₂) :
    isoClassMk L₁ = isoClassMk L₂ := sorry

/-- Action of an Ext¹ class on an isomorphism class, via `translate`. -/
def vadd (ξ : extOneNL t f) (p : IsoClass t f) : IsoClass t f :=
  Quotient.map (translate ξ) sorry p

/-- Difference of isomorphism classes, as an Ext¹ class. Subtraction is oriented
so that `[X'_ξ] -ᵥ [X'] = ξ` when `o(X', X'_ξ) = ξ`. -/
def vsub (p q : IsoClass t f) : extOneNL t f :=
  Quotient.lift₂ (fun L₁ L₂ ↦ liftObstruction L₂ L₁) sorry p q

/-- Ext¹ classes act on isomorphism classes of flat lifts by translation. -/
@[reducible] def vaddStructure : VAdd (extOneNL t f) (IsoClass t f) where
  vadd := vadd

/-- Difference of isomorphism classes of flat lifts is an Ext¹ class. -/
@[reducible] def vsubStructure : VSub (extOneNL t f) (IsoClass t f) where
  vsub := vsub

/-- The Ext¹-action of naive cotangent classes on isomorphism classes of flat
lifts. -/
@[reducible] def addAction : AddAction (extOneNL t f) (IsoClass t f) where
  vadd := vadd
  add_vadd := sorry
  zero_vadd := sorry

/-- The Ext¹-action computes on representatives by `translate`. -/
theorem vadd_mk (ξ : extOneNL t f) (L : FlatLift t f) :
    vadd ξ (isoClassMk L) = isoClassMk (translate ξ L) := sorry

/-- Torsor subtraction computes on representatives by the reversed obstruction. -/
theorem vsub_mk (L₁ L₂ : FlatLift t f) :
    vsub (isoClassMk L₁) (isoClassMk L₂) = liftObstruction L₂ L₁ := sorry

/-- The zero Ext¹ class acts as the identity on isomorphism classes. -/
theorem vadd_zero (p : IsoClass t f) :
    vadd (0 : extOneNL t f) p = p := sorry

/-- The Ext¹-action is compatible with addition. -/
theorem add_vadd (ξ η : extOneNL t f) (p : IsoClass t f) :
    vadd (ξ + η) p = vadd ξ (vadd η p) := sorry

/-- With a chosen flat lift as basepoint, isomorphism classes are an additive
torsor under Ext¹(NL[f], f^* 𝒞_{Y/Y'}). -/
@[reducible]
def addTorsor (S0 : FlatLift t f) : AddTorsor (extOneNL t f) (IsoClass t f) where
  toAddAction := addAction
  toVSub := vsubStructure
  nonempty := ⟨isoClassMk S0⟩
  vsub_vadd' := sorry
  vadd_vsub' := sorry

/-- Translation from a chosen lift identifies Ext¹ with the isomorphism classes of flat lifts. -/
def isoClassEquiv (S0 : FlatLift t f) : extOneNL t f ≃ IsoClass t f :=
  @Equiv.vaddConst _ _ _ (addTorsor S0) (isoClassMk S0)

/-- The based chart sends an Ext¹ class ξ to the translate of the basepoint. -/
theorem isoClassEquiv_apply (S0 : FlatLift t f) (ξ : extOneNL t f) :
    isoClassEquiv S0 ξ = vadd ξ (isoClassMk S0) := sorry

/-- The zero Ext¹ class is sent to the class of the basepoint. -/
theorem isoClassEquiv_zero (S0 : FlatLift t f) :
    isoClassEquiv S0 0 = isoClassMk S0 := sorry

/-- The inverse chart is torsor subtraction against the basepoint. -/
theorem isoClassEquiv_symm_apply (S0 : FlatLift t f) (p : IsoClass t f) :
    (isoClassEquiv S0).symm p = vsub p (isoClassMk S0) := sorry

end FlatLift
end AlgebraicGeometry.AlgebraicSpace.Thickening
