/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.Lemma_91_7_8_Extension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibre chart of isomorphism classes of first-order ringed-space solutions

In the 91.7.0.1 first-order ringed-space diagram, isomorphism classes of
solutions are canonically parametrized by the fibre of `extOne_comap t f`
over the image of the tautological class ξ.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Solution

variable {S S' X : RingedSpace.{u}}
variable (t : S ⟶ S') [IsFirstOrderThickening t]
variable (f : X ⟶ S) (G : X.Modules)
variable (c : Hom.idealModule t ⟶ (f _*).obj G)

/-- Lemma 91.7.8 Let t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'}), 𝒥 = Ker(t^♯),
f : (X, 𝒪_X) ⟶ (S, 𝒪_S), 𝒢, and c : 𝒥 ⟶ 𝒢 be as in 91.7.0.1.
Denote ξ ∈ Ext¹_{𝒪_S}(NL_{S/S'}, 𝒥) the element corresponding to the
extension 𝒪_{S'} of 𝒪_S by 𝒥 via Lemma 91.7.4. The set of isomorphism classes
of solutions is canonically bijective to the fibre of
Ext¹_{𝒪_X}(NL_{X/S'}, 𝒢) ⟶ Ext¹_{𝒪_X}(L(f)^* NL_{S/S'}, 𝒢) over the image of ξ.
Here 𝒥 is `Hom.idealModule t`, ξ is `selfExtensionClass t`, the Ext¹ groups are
`Ext⁽1⁾(Q NL[f ≫ t], Q(𝒢[0]))` and `Ext⁽1⁾(L(f)^* NL[t], Q(𝒢[0]))`, the
displayed map is `extOne_comap t f`, the image of ξ is
`extOne_map (cPull t f c) (selfExtensionClass t)`, and the fibre is
`solutionExtFiber t f G c`. -/
@[stacks 0GQ3]
def isoClassFiberEquiv : IsoClass t f G c ≃ solutionExtFiber t f G c where
  toFun p := ⟨toExtClass t f G c p, sorry⟩
  invFun := ofFiber t f G c
  left_inv := sorry
  right_inv := sorry

/-- The fibre chart sends an isomorphism class to its Ext¹ class in the fibre. -/
theorem isoClassFiberEquiv_apply (p : IsoClass t f G c) :
    (isoClassFiberEquiv t f G c p).val = toExtClass t f G c p := sorry

/-- The inverse fibre chart is `ofFiber`. -/
theorem isoClassFiberEquiv_symm_apply (ζ : solutionExtFiber t f G c) :
    (isoClassFiberEquiv t f G c).symm ζ = ofFiber t f G c ζ := sorry

/-- Solutions exist if and only if the image of ξ lies in the image of restriction. -/
theorem isoClassFiberEquiv_nonempty_iff :
    Nonempty (IsoClass t f G c) ↔ Nonempty (solutionExtFiber t f G c) := sorry

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
