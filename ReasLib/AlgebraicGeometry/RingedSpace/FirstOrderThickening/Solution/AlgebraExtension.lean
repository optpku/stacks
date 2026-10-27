/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Split
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Torsor

/-!
# Classification of square-zero algebra extensions of ringed spaces

The split extension canonically identifies the Ext¹ group of the naive cotangent complex
with isomorphism classes of relative square-zero algebra extensions with fixed kernel.
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

/-- Relative square-zero algebra extensions with identified kernel `G` are canonically
classified by Ext¹ of the naive cotangent complex with coefficients in `G`. -/
def extensionEquiv :
    Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)) ≃
      IsoClass (𝟙 S) f G (zeroKernelMap f G) :=
  isoClassEquiv (trivialSolution f G)

/-- The based chart sends an Ext¹ class ξ to the translate of the split extension. -/
theorem extensionEquiv_apply
    (ξ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := X.Modules)).obj NL[f],
      (DerivedCategory.Q (C := X.Modules)).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) :
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

/-- The canonical classification is the torsor chart at the split solution. -/
theorem extensionEquiv_eq_isoClassEquiv :
    extensionEquiv f G = isoClassEquiv (trivialSolution f G) := sorry

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
