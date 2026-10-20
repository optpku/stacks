/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.Lemma_91_8_1_IsoClass
public import stacks_project.Chap91.Lemma_91_8_1_Lift
public import stacks_project.Chap91.Lemma_91_8_1_Translate
import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal homogeneous space of flat first-order deformations of schemes

If `S ⊂ S'` is a first-order thickening of schemes and `f : X ⟶ S` is flat,
and there exists a flat `f' : X' ⟶ S'` with an `S`-isomorphism
`a : X ≅ X' ×_{S'} S`, then isomorphism classes of such pairs are principal
homogeneous under Ext¹_{𝒪_X}(NL[X/S], f^* 𝒞_{S/S'}), and automorphisms of a
given `X'` over `S'` reducing to the identity on `X' ×_{S'} S` are
Ext⁰_{𝒪_X}(NL[X/S], f^* 𝒞_{S/S'}).
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Thickening
open AlgebraicGeometry.Scheme.Thickening.FlatLift
open scoped AlgebraicGeometry DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Thickening
namespace FlatLift

variable {S S' X : Scheme.{u}}
variable {t : S ⟶ S'} [IsFirstOrderThickening t] {f : X ⟶ S} [Flat f]

/-- Lemma 91.8.1 (1) Let `S ⊂ S'` be a first-order thickening of schemes. Let
`f : X ⟶ S` be a flat morphism of schemes. If there exists a flat morphism
`f' : X' ⟶ S'` of schemes and an isomorphism `a : X ≅ X' ×_{S'} S` over `S`,
then the set of isomorphism classes of pairs `(f' : X' ⟶ S', a)` is principal
homogeneous under Ext¹_{𝒪_X}(NL[X/S], f^* 𝒞_{S/S'}). Existence is the basepoint
`S0`; the acting group is Ext¹(Q NL[f], Q((f^* 𝒞_{S/S'})[0])). -/
@[stacks 0D14]
def isoClassEquiv (S0 : FlatLift t f) : extOneNL t f ≃ IsoClass t f where
  toFun ξ := ξ +ᵥ isoClassMk S0
  invFun p := p -ᵥ isoClassMk S0
  left_inv := sorry
  right_inv := sorry

/-- The based chart sends an Ext¹ class ξ to the translate of the basepoint. -/
theorem isoClassEquiv_apply (S0 : FlatLift t f) (ξ : extOneNL t f) :
    isoClassEquiv S0 ξ = ξ +ᵥ isoClassMk S0 := sorry

/-- The zero Ext¹ class is sent to the class of the basepoint. -/
theorem isoClassEquiv_zero (S0 : FlatLift t f) :
    isoClassEquiv S0 0 = isoClassMk S0 := sorry

/-- The inverse chart is torsor subtraction against the basepoint. -/
theorem isoClassEquiv_symm_apply (S0 : FlatLift t f) (p : IsoClass t f) :
    (isoClassEquiv S0).symm p = p -ᵥ isoClassMk S0 := sorry

/-- Lemma 91.8.1 (2) Let `S ⊂ S'` be a first-order thickening of schemes. Let
`f : X ⟶ S` be a flat morphism of schemes. If there exists a flat morphism
`f' : X' ⟶ S'` of schemes and an isomorphism `a : X ≅ X' ×_{S'} S` over `S`,
then the set of automorphisms of a given `X'` over `S'` which reduce to the
identity on `X' ×_{S'} S` is Ext⁰_{𝒪_X}(NL[X/S], f^* 𝒞_{S/S'}). -/
@[stacks 0D14]
def reduceIdAutoEquiv (L : FlatLift t f) : ReduceIdAuto L ≃ extZeroNL t f where
  toFun φ := toExtZero φ
  invFun ξ := ofExtZero L ξ
  left_inv := sorry
  right_inv := sorry

/-- The forward chart sends a reducing-to-identity automorphism to its Ext⁰ class. -/
theorem reduceIdAutoEquiv_apply (L : FlatLift t f) (φ : ReduceIdAuto L) :
    reduceIdAutoEquiv L φ = toExtZero φ := sorry

/-- The inverse chart sends an Ext⁰ class to the identity-cube perturbation of
the identity automorphism. -/
theorem reduceIdAutoEquiv_symm_apply (L : FlatLift t f) (ξ : extZeroNL t f) :
    (reduceIdAutoEquiv L).symm ξ = ofExtZero L ξ := sorry

/-- The identity automorphism is sent to the zero Ext⁰ class. -/
theorem reduceIdAutoEquiv_zero (L : FlatLift t f) :
    reduceIdAutoEquiv L (ReduceIdAuto.id L) = 0 := sorry

end FlatLift
end AlgebraicGeometry.Scheme.Thickening
