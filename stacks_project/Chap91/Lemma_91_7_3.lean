/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Lemma_91_7_3_Translate
public import stacks_project.Chap91.Lemma_91_7_3_IsoClass
import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal homogeneous space of first-order ringed-space solutions

If a diagram 91.7.0.1 admits at least one solution, isomorphism classes of
solutions are principal homogeneous under Ext⁽1⁾(Q NL[f], Q(𝒢[0])).
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Solution

variable {S S' X : RingedSpace.{u}} {t : S ⟶ S'} [IsFirstOrderThickening t] {f : X ⟶ S}
variable {G : X.Modules} {c : Hom.idealModule t ⟶ (f _*).obj G}

/-- Lemma 91.7.3 If there exists a solution to 91.7.0.1, then the set of
isomorphism classes of solutions is principal homogeneous under
Ext⁽1⁾_{𝒪_X}(NL[f], 𝒢). Existence is the basepoint S0; the acting group is
Ext⁽1⁾(Q NL[f], Q(𝒢[0])). -/
@[stacks 08UC]
def isoClassEquiv (S0 : Solution t f G c) :
    Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)) ≃
      IsoClass t f G c where
  toFun ξ := ξ +ᵥ isoClassMk S0
  invFun p := p -ᵥ isoClassMk S0
  left_inv := sorry
  right_inv := sorry

/-- The based chart sends an Ext¹ class ξ to the translate of the basepoint. -/
theorem isoClassEquiv_apply (S0 : Solution t f G c)
    (ξ : Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G))) :
    isoClassEquiv S0 ξ = ξ +ᵥ isoClassMk S0 := sorry

/-- The zero Ext¹ class is sent to the class of the basepoint. -/
theorem isoClassEquiv_zero (S0 : Solution t f G c) :
    isoClassEquiv S0 0 = isoClassMk S0 := sorry

/-- The inverse chart is torsor subtraction against the basepoint. -/
theorem isoClassEquiv_symm_apply (S0 : Solution t f G c) (p : IsoClass t f G c) :
    (isoClassEquiv S0).symm p = p -ᵥ isoClassMk S0 := sorry

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
