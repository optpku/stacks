/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.Translate

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.NaiveCotangent
open HomologicalComplex DerivedCategory
open Opposite TrivSqZeroExt
open scoped DerivedExt SheafOfModules.RingedSite
open scoped CategoryTheory.Sheaf.FreeAlgebra

noncomputable section

universe c v w

namespace SheafOfModules.RingedSite.FirstOrderThickening
namespace Solution

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and Ext must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] HasDerivedCategory.standard

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O_B' O_B O : Sheaf J CommRingCat.{w}}
variable {π : O_B' ⟶ O_B} [Sheaf.IsLocallySurjective π]
variable {hπ : KernelIdeal.IsSquareZero π}
variable {fSharp : O_B ⟶ O}
variable {G : SheafOfModules (ringSheaf J O)}
variable {c :
    hπ.targetModule (KernelIdeal.quotientComparison_isIso π) ⟶
      (restrictionAlong fSharp).obj G}

section Of

variable (E : Sheaf J (Type w))
variable (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
variable (δ : (Presentation.ofGenerators E α).X (-1) ⟶ G)
variable [IsLocallySurjective (FreeAlgebra.evaluation (Under.mk fSharp) E α).right]

/-- Invert the specified coefficient inclusion; no global section lift is selected. -/
def translateKernelIso (sol : Solution π hπ fSharp G c) :
    (translateProj_squareZero E α δ sol).targetModule
      (@KernelIdeal.quotientComparison_isIso _ _ _ _ _ _ _
        (translateProj E α δ sol) _ (instIsLocallySurjective_translateProj E α δ sol)) ≅ G :=
  translateKernelIsoOf E α δ sol (translateKernelInclusion_isIso E α δ sol)

/-- Choice-free constructor: the pushout of `O_{B'}[E ×_O O']` along `ψ = φ|_{I'} + δ`
for an explicit 91.13.2 conormal representative `δ`. -/
def translateOf (sol : Solution π hπ fSharp G c) :
    Solution π hπ fSharp G c :=
  translateOfWith E α δ sol (translateKernelInclusion_isIso E α δ sol)

/-- The translate of a solution along an explicit conormal map is again a solution of
91.13.0.1, with structure sheaf the pushout of `O_{B'}[E ×_O O']` along `ψ`. -/
theorem translateOf_spec (sol : Solution π hπ fSharp G c) :
    (translateOf E α δ sol).middle = translateSheaf E α δ sol ∧
      (translateOf E α δ sol).proj = translateProj E α δ sol ∧
        (translateOf E α δ sol).structureMap = translateStructureMap E α δ sol := by
  exact translateOfWith_spec E α δ sol (translateKernelInclusion_isIso E α δ sol)

end Of

/-- Pushout translate of a solution along an Ext¹ class, using a 91.13.2 conormal
representative internally. -/
def translate
    (ξ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (DerivedCategory.Q).obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (sol : Solution π hπ fSharp G c) :
    Solution π hπ fSharp G c :=
  let h := exists_conormalHomClass fSharp G ξ
  let E := Classical.choose h
  let hα := Classical.choose_spec h
  let α := Classical.choose hα
  let hP := Classical.choose_spec hα
  -- Local instance justification (proof-local temporary data): hP.1 is the local-surjectivity certificate for the exact E and alpha chosen from exists_conormalHomClass; translateOf consumes that certificate for the same polynomial presentation.
  letI := hP.1
  translateOf E α (Classical.choose hP.2) sol

/-- `translate ξ sol` is `translateOf` of some 91.13.2 representative of ξ. -/
theorem translate_spec
    (ξ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q).obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
      (DerivedCategory.Q).obj ((CochainComplex.singleFunctor _ 0).obj G)))
    (sol : Solution π hπ fSharp G c) :
    ∃ (E : Sheaf J (Type w))
      (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp))
      (h : IsLocallySurjective (FreeAlgebra.evaluation (Under.mk fSharp) E α).right)
      (δ : (Presentation.ofGenerators E α).X (-1) ⟶ G),
        -- Local instance justification (proof-local temporary data): the existential h certifies this displayed evaluation map; it supplies the required instance for derivedComparison and translateOf in the same witness specification.
        letI := h;
        Presentation.derivedComparison E α ≫ ξ = conormalHomClass fSharp G E α δ ∧
          translate ξ sol = translateOf E α δ sol := by
  let h := exists_conormalHomClass fSharp G ξ
  let E := Classical.choose h
  let hα := Classical.choose_spec h
  let α := Classical.choose hα
  let hP := Classical.choose_spec hα
  exact ⟨E, α, hP.1, Classical.choose hP.2, Classical.choose_spec hP.2, rfl⟩


end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
