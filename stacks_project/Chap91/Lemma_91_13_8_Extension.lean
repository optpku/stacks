/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Lemma_91_13_4
public import stacks_project.Chap91.Lemma_91_13_6_Map

/-!
# Tautological first-order thickening and the Ext¹ fibre of solutions

The identity-diagram solution with middle ring sheaf `O_B'` classifies `π` as an
`O_B'`-algebra extension of `O_B` by `Ker π`. Forgetting a solution of 91.13.0.1
to an `f⁻¹ O_B'`-algebra extension of `O` by `G` lands in the fibre of
`extOne_comap π fSharp` over the image of that class along the adjunct of `c`.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.FirstOrderThickening.Solution
open SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace Solution

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and Ext must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O_B' O_B O : Sheaf J CommRingCat.{u}}
variable (π : O_B' ⟶ O_B) [Sheaf.IsLocallySurjective π]
variable (hπ : KernelIdeal.IsSquareZero π)
variable (fSharp : O_B ⟶ O)
variable (G : SheafOfModules (ringSheaf J O))
variable (c :
    hπ.targetModule (KernelIdeal.quotientComparison_isIso π) ⟶
      (restrictionAlong fSharp).obj G)

/-- The O-linear adjunct of an O_B-linear coefficient map
`c : Ker π ⟶ (restrictionAlong fSharp).obj G`. -/
def extendCoeff :
    (extendAlong fSharp).obj
        (hπ.targetModule (KernelIdeal.quotientComparison_isIso π)) ⟶ G :=
  ((extendRestrictAdj fSharp).homEquiv
      (hπ.targetModule (KernelIdeal.quotientComparison_isIso π)) G).symm c

/-- `extendCoeff` is the inverse adjunction unit of `extendRestrictAdj fSharp`. -/
theorem extendCoeff_spec :
    extendCoeff π hπ fSharp G c =
      ((extendRestrictAdj fSharp).homEquiv
          (hπ.targetModule (KernelIdeal.quotientComparison_isIso π)) G).symm c :=
  sorry

/-- The tautological identity-diagram solution, with middle ring sheaf `O_B'`. -/
def selfSolution :
    Solution (𝟙 O_B') (isSquareZero_id O_B') π
      (hπ.targetModule (KernelIdeal.quotientComparison_isIso π))
      (zeroKernelMap π (hπ.targetModule (KernelIdeal.quotientComparison_isIso π))) where
  middle := O_B'
  proj := π
  structureMap := 𝟙 O_B'
  proj_locallySurjective := inferInstance
  proj_squareZero := hπ
  proj_quotient_isIso := KernelIdeal.quotientComparison_isIso π
  commutes := rfl
  kernelIso := Iso.refl _
  induces_c := sorry

/-- The carrier of the tautological solution is `O_B'`. -/
theorem selfSolution_middle : (selfSolution π hπ).middle = O_B' := sorry

/-- The projection of the tautological solution is `π`. -/
theorem selfSolution_proj : (selfSolution π hπ).proj = π := sorry

/-- The structure map of the tautological solution is the identity on `O_B'`. -/
theorem selfSolution_structureMap : (selfSolution π hπ).structureMap = 𝟙 O_B' := sorry

/-- The Ext¹ class ξ of the tautological extension `O_B'` of `O_B` by `Ker π`. -/
def selfExtensionClass :
    Ext⁽(1 : ℤ)⁾((moduleQ O_B).obj (NaiveCotangent.obj O_B' (Under.mk π)),
      (moduleQ O_B).obj
        ((CochainComplex.singleFunctor _ 0).obj
          (hπ.targetModule (KernelIdeal.quotientComparison_isIso π)))) :=
  (extensionEquiv π
      (hπ.targetModule (KernelIdeal.quotientComparison_isIso π))).symm
    (isoClassMk (selfSolution π hπ))

/-- `selfExtensionClass` is the inverse identity-diagram chart of `selfSolution`. -/
theorem selfExtensionClass_spec :
    selfExtensionClass π hπ =
      (extensionEquiv π
          (hπ.targetModule (KernelIdeal.quotientComparison_isIso π))).symm
        (isoClassMk (selfSolution π hπ)) :=
  sorry

/-- Forget a solution of 91.13.0.1 to an `f⁻¹ O_B'`-algebra extension of `O` by `G`. -/
def toIdentitySolution (S : Solution π hπ fSharp G c) :
    Solution (𝟙 O_B') (isSquareZero_id O_B') (π ≫ fSharp) G
      (zeroKernelMap (π ≫ fSharp) G) where
  middle := S.middle
  proj := S.proj
  structureMap := S.structureMap
  proj_locallySurjective := S.proj_locallySurjective
  proj_squareZero := S.proj_squareZero
  proj_quotient_isIso := S.proj_quotient_isIso
  commutes := sorry
  kernelIso := S.kernelIso
  induces_c := sorry

/-- Forgetting to the identity diagram preserves the middle ring sheaf. -/
theorem toIdentitySolution_middle (S : Solution π hπ fSharp G c) :
    (toIdentitySolution π hπ fSharp G c S).middle = S.middle := sorry

/-- Forgetting to the identity diagram preserves the projection onto `O`. -/
theorem toIdentitySolution_proj (S : Solution π hπ fSharp G c) :
    (toIdentitySolution π hπ fSharp G c S).proj = S.proj := sorry

/-- Forgetting to the identity diagram preserves the structure map from `O_B'`. -/
theorem toIdentitySolution_structureMap (S : Solution π hπ fSharp G c) :
    (toIdentitySolution π hπ fSharp G c S).structureMap = S.structureMap := sorry

/-- The Ext¹ class in `Ext¹_O(NL_{O/O_B'}, G)` attached to an isomorphism class of solutions. -/
def toExtClass (p : IsoClass π hπ fSharp G c) :
    Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B' (Under.mk (π ≫ fSharp))),
      (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  Quotient.liftOn p
    (fun S ↦
      (extensionEquiv (π ≫ fSharp) G).symm
        (isoClassMk (toIdentitySolution π hπ fSharp G c S)))
    sorry

/-- `toExtClass` on a solution representative is the inverse identity-diagram chart. -/
theorem toExtClass_mk (S : Solution π hπ fSharp G c) :
    toExtClass π hπ fSharp G c (isoClassMk S) =
      (extensionEquiv (π ≫ fSharp) G).symm
        (isoClassMk (toIdentitySolution π hπ fSharp G c S)) :=
  sorry

/-- The fibre of `Ext¹_O(NL_{O/O_B'}, G) ⟶ Ext¹_O(Lf^* NL_{O_B/O_B'}, G)` over the image of ξ. -/
abbrev solutionExtFiber :=
  {ζ :
      Ext⁽(1 : ℤ)⁾((moduleQ O).obj (NaiveCotangent.obj O_B' (Under.mk (π ≫ fSharp))),
        (moduleQ O).obj ((CochainComplex.singleFunctor _ 0).obj G)) //
    extOne_comap π fSharp ζ =
      extOne_map (extendCoeff π hπ fSharp G c) (selfExtensionClass π hπ)}

/-- Membership in `solutionExtFiber` is `extOne_comap π fSharp` equalling the image of ξ. -/
theorem mem_solutionExtFiber (ζ : solutionExtFiber π hπ fSharp G c) :
    extOne_comap π fSharp ζ.val =
      extOne_map (extendCoeff π hπ fSharp G c) (selfExtensionClass π hπ) :=
  sorry

/-- Repackage a fibre representative as an isomorphism class of solutions of 91.13.0.1. -/
def ofFiber (ζ : solutionExtFiber π hπ fSharp G c) : IsoClass π hπ fSharp G c :=
  Quotient.liftOn (extensionEquiv (π ≫ fSharp) G ζ.val)
    (fun SB ↦
      isoClassMk
        { middle := SB.middle
          proj := SB.proj
          structureMap := SB.structureMap
          proj_locallySurjective := SB.proj_locallySurjective
          proj_squareZero := SB.proj_squareZero
          proj_quotient_isIso := SB.proj_quotient_isIso
          commutes := sorry
          kernelIso := SB.kernelIso
          induces_c := sorry })
    sorry

/-- The forgetful Ext¹ class of `ofFiber ζ` recovers the fibre representative. -/
theorem toExtClass_ofFiber (ζ : solutionExtFiber π hπ fSharp G c) :
    toExtClass π hπ fSharp G c (ofFiber π hπ fSharp G c ζ) = ζ.val := sorry

end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
