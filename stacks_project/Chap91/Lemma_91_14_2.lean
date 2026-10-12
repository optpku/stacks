/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Lemma_91_14_2_Ext1
public import stacks_project.Chap91.Lemma_91_14_2_Ext1Geometric
public import stacks_project.Chap91.Lemma_91_14_2_FlatKernel
public import stacks_project.Chap91.Lemma_91_14_2_GeometricNL
public import stacks_project.Chap91.Lemma_91_14_2_GeometricNLComparison
public import stacks_project.Chap91.Lemma_91_14_2_KernelBridge
public import stacks_project.Chap91.Lemma_91_14_2_LiftAlgebra
public import stacks_project.Chap91.Lemma_91_14_2_SmallKernel
public import stacks_project.Chap91.Lemma_91_14_2_SolutionBridge
public import stacks_project.Chap91.Lemma_91_14_2_UniversalDerivation

public import stacks_project.Chap91.Lemma_91_14_2_IsoClass
public import stacks_project.Chap91.Lemma_91_14_2_Lift
public import stacks_project.Chap91.Lemma_91_14_2_Translate
import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal homogeneous space of flat first-order deformations of algebraic spaces

If `Y ⊂ Y'` is a first-order thickening of algebraic spaces over a scheme `S`
and `f : X ⟶ Y` is flat, and there exists a flat `f' : X' ⟶ Y'` with a
`Y`-isomorphism `a : X ≅ X' ×_{Y'} Y`, then isomorphism classes of such pairs
are principal homogeneous under Ext¹_{𝒪_X}(NL[X/Y], f^* 𝒞_{Y/Y'}), and
automorphisms of a given `X'` over `Y'` reducing to the identity on
`X' ×_{Y'} Y` are Ext⁰_{𝒪_X}(NL[X/Y], f^* 𝒞_{Y/Y'}).
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Thickening
open AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift
open scoped AlgebraicGeometry.AlgebraicSpace DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening
namespace FlatLift

variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}
variable {t : Y ⟶ Y'} [IsFirstOrderThickening t] {f : X ⟶ Y} [Flat f]

/-- Lemma 91.14.2 (1) Let `S` be a scheme. Let `Y ⊂ Y'` be a first-order thickening
of algebraic spaces over `S`. Let `f : X ⟶ Y` be a flat morphism of algebraic
spaces over `S`. If there exists a flat morphism `f' : X' ⟶ Y'` of algebraic
spaces over `S` and an isomorphism `a : X ≅ X' ×_{Y'} Y` over `Y`, then the set
of isomorphism classes of pairs `(f' : X' ⟶ Y', a)` is principal homogeneous
under Ext¹_{𝒪_X}(NL[X/Y], f^* 𝒞_{Y/Y'}). Existence is the basepoint `S0`; the
acting group is Ext¹(Q NL[f], Q((f^* 𝒞_{Y/Y'})[0])). -/
@[stacks 0D17]
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

/-- Lemma 91.14.2 (2) Let `S` be a scheme. Let `Y ⊂ Y'` be a first-order thickening
of algebraic spaces over `S`. Let `f : X ⟶ Y` be a flat morphism of algebraic
spaces over `S`. If there exists a flat morphism `f' : X' ⟶ Y'` of algebraic
spaces over `S` and an isomorphism `a : X ≅ X' ×_{Y'} Y` over `Y`, then the set
of automorphisms of a given `X'` over `Y'` which reduce to the identity on
`X' ×_{Y'} Y` is Ext⁰_{𝒪_X}(NL[X/Y], f^* 𝒞_{Y/Y'}). -/
@[stacks 0D17]
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
end AlgebraicGeometry.AlgebraicSpace.Thickening
