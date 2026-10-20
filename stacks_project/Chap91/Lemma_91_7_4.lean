/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.Lemma_91_7_4_Trivial
public import stacks_project.Chap91.Lemma_91_7_3
import Mathlib.Tactic.CrossRefAttribute

/-!
# Classification of square-zero f⁻¹𝒪_S-algebra extensions of 𝒪_X by 𝒢

Isomorphism classes of extensions 0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0 of f⁻¹𝒪_S-algebras
in which 𝒢 is an ideal of square zero are canonically bijective to
Ext¹_{𝒪_X}(NL_{X/S}, 𝒢), by specializing the torsor chart of Lemma 91.7.3 to
the identity diagram and the split solution 𝒢 ⊕ 𝒪_X.
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

variable {S X : RingedSpace.{u}} (f : X ⟶ S) (G : X.Modules)

/-- Lemma 91.7.4 Let f : (X, 𝒪_X) ⟶ (S, 𝒪_S) be a morphism of ringed spaces.
Let 𝒢 be an 𝒪_X-module. The set of isomorphism classes of extensions of
f⁻¹𝒪_S-algebras 0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0 where 𝒢 is an ideal of square zero
is canonically bijective to Ext¹_{𝒪_X}(NL_{X/S}, 𝒢). The Ext¹ group is
Ext⁽1⁾(Q NL[f], Q(𝒢[0])), and the classes are
`IsoClass (𝟙 S) f G (zeroKernelMap f G)`, based at the split solution
`trivialSolution f G`. -/
@[stacks 0GPZ]
def extensionEquiv :
    Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)) ≃
      IsoClass (𝟙 S) f G (zeroKernelMap f G) :=
  isoClassEquiv (trivialSolution f G)

/-- The based chart sends an Ext¹ class ξ to the translate of the split extension. -/
theorem extensionEquiv_apply
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) :
    extensionEquiv f G ξ =
      ξ +ᵥ isoClassMk (trivialSolution f G) := sorry

/-- The zero Ext¹ class is sent to the class of the split extension 𝒢 ⊕ 𝒪_X. -/
theorem extensionEquiv_zero :
    extensionEquiv f G 0 = isoClassMk (trivialSolution f G) := sorry

/-- The inverse chart is torsor subtraction against the split extension. -/
theorem extensionEquiv_symm_apply
    (p : IsoClass (𝟙 S) f G (zeroKernelMap f G)) :
    (extensionEquiv f G).symm p =
      p -ᵥ isoClassMk (trivialSolution f G) := sorry

/-- The source bijection is the torsor chart of Lemma 91.7.3 at the split solution. -/
theorem extensionEquiv_eq_isoClassEquiv :
    extensionEquiv f G = isoClassEquiv (trivialSolution f G) := sorry

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
