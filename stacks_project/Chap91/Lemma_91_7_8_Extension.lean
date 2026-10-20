/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.Lemma_91_7_4
public import stacks_project.Chap91.Lemma_91_7_6_Map
public import stacks_project.Chap91.«91_7_0_1_Solution»

/-!
# Tautological first-order thickening and the Ext¹ fibre of solutions

The identity-diagram solution with middle space `S'` classifies `t` as an
`𝒪_{S'}`-algebra extension of `𝒪_S` by `Ker(t^♯)`. Forgetting a solution of
91.7.0.1 to an `f⁻¹ 𝒪_{S'}`-algebra extension of `𝒪_X` by `𝒢` lands in the
fibre of `extOne_comap t f` over the image of that class along `cPull t f c`.
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

/-- The tautological solution of the identity diagram, with middle space `S'`. -/
def selfSolution : Solution (𝟙 S') t (Hom.idealModule t) (zeroKernelMap t (Hom.idealModule t)) :=
  Solution.of (𝟙 S') t (Hom.idealModule t) (zeroKernelMap t (Hom.idealModule t))
    t (𝟙 S') rfl (Iso.refl _) sorry

/-- The carrier of the tautological solution is `S'`. -/
theorem selfSolution_space : (selfSolution t).space = S' := sorry

/-- The thickening of the tautological solution is `t`. -/
theorem selfSolution_i : (selfSolution t).i = t := sorry

/-- The structure map of the tautological solution is the identity on `S'`. -/
theorem selfSolution_f' : (selfSolution t).f' = 𝟙 S' := sorry

/-- The Ext¹ class ξ of the tautological extension `𝒪_{S'}` of `𝒪_S` by `𝒥`. -/
def selfExtensionClass :
    Ext⁽(1 : ℤ)⁾((moduleQ S).obj NL[t],
      (moduleQ S).obj
        ((CochainComplex.singleFunctor S.Modules 0).obj (Hom.idealModule t))) :=
  (extensionEquiv t (Hom.idealModule t)).symm (isoClassMk (selfSolution t))

/-- `selfExtensionClass` is the inverse identity-diagram chart of `selfSolution`. -/
theorem selfExtensionClass_spec :
    selfExtensionClass t =
      (extensionEquiv t (Hom.idealModule t)).symm (isoClassMk (selfSolution t)) :=
  sorry

/-- Forget a solution of 91.7.0.1 to an `f⁻¹ 𝒪_{S'}`-algebra extension of `𝒪_X` by `𝒢`. -/
def toIdentitySolution (sol : Solution t f G c) :
    Solution (𝟙 S') (f ≫ t) G (zeroKernelMap (f ≫ t) G) where
  space := sol.space
  i := sol.i
  i_isFirstOrder := sol.i_isFirstOrder
  f' := sol.f'
  commutes := sorry
  kernelIso := sol.kernelIso
  induces_c := sorry

/-- Forgetting to the identity diagram preserves the middle ringed space. -/
theorem toIdentitySolution_space (sol : Solution t f G c) :
    (toIdentitySolution t f G c sol).space = sol.space := sorry

/-- Forgetting to the identity diagram preserves the thickening of `X`. -/
theorem toIdentitySolution_i (sol : Solution t f G c) :
    (toIdentitySolution t f G c sol).i = sol.i := sorry

/-- Forgetting to the identity diagram preserves the structure map to `S'`. -/
theorem toIdentitySolution_f' (sol : Solution t f G c) :
    (toIdentitySolution t f G c sol).f' = sol.f' := sorry

/-- The Ext¹ class in `Ext¹_{𝒪_X}(NL_{X/S'}, 𝒢)` attached to an isomorphism class of solutions. -/
def toExtClass (p : IsoClass t f G c) :
    Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f ≫ t],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)) :=
  Quotient.liftOn p
    (fun sol ↦
      (extensionEquiv (f ≫ t) G).symm (isoClassMk (toIdentitySolution t f G c sol)))
    sorry

/-- `toExtClass` on a solution representative is the inverse identity-diagram chart. -/
theorem toExtClass_mk (sol : Solution t f G c) :
    toExtClass t f G c (isoClassMk sol) =
      (extensionEquiv (f ≫ t) G).symm (isoClassMk (toIdentitySolution t f G c sol)) :=
  sorry

/-- The fibre of `Ext¹_{𝒪_X}(NL_{X/S'}, 𝒢) ⟶ Ext¹_{𝒪_X}(L(f)^* NL_{S/S'}, 𝒢)` over the image of ξ. -/
abbrev solutionExtFiber :=
  {ζ :
      Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f ≫ t],
        (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj G)) //
    extOne_comap t f ζ = extOne_map (cPull t f c) (selfExtensionClass t)}

/-- Membership in `solutionExtFiber` is `extOne_comap t f` equalling the image of ξ. -/
theorem mem_solutionExtFiber (ζ : solutionExtFiber t f G c) :
    extOne_comap t f ζ.val = extOne_map (cPull t f c) (selfExtensionClass t) :=
  sorry

/-- Repackage a fibre representative as an isomorphism class of solutions of 91.7.0.1. -/
def ofFiber (ζ : solutionExtFiber t f G c) : IsoClass t f G c :=
  Quotient.liftOn (extensionEquiv (f ≫ t) G ζ.val)
    (fun SB ↦
      isoClassMk (Solution.of t f G c SB.i SB.f' sorry SB.kernelIso sorry))
    sorry

/-- The forgetful Ext¹ class of `ofFiber ζ` recovers the fibre representative. -/
theorem toExtClass_ofFiber (ζ : solutionExtFiber t f G c) :
    toExtClass t f G c (ofFiber t f G c ζ) = ζ.val := sorry

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
