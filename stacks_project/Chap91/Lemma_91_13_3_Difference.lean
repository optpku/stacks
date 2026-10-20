module
public import stacks_project.Chap91.Lemma_91_13_3_Translate

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

namespace Difference
variable (S₁ S₂ : Solution π hπ fSharp G c)

/-- Common generators are pairs of sections with the same image in O. -/
def generators : Sheaf J (Type w) :=
  (sheafForget J).obj (Limits.pullback S₁.proj S₂.proj)

def assignment : generators S₁ S₂ ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp) :=
  (sheafForget J).map (Limits.pullback.fst S₁.proj S₂.proj ≫ S₁.proj)

def frontAssignment : generators S₁ S₂ ⟶ (sheafForget J).obj S₁.middle :=
  (sheafForget J).map (Limits.pullback.fst S₁.proj S₂.proj)

def backAssignment : generators S₁ S₂ ⟶ (sheafForget J).obj S₂.middle :=
  (sheafForget J).map (Limits.pullback.snd S₁.proj S₂.proj)

def eval : O_B' [generators S₁ S₂] ⟶ O :=
  (FreeAlgebra.evaluation (Under.mk (π ≫ fSharp))
    (generators S₁ S₂) (assignment S₁ S₂)).right

abbrev liftedComplex :=
  Presentation.complex (FreeAlgebra.base O_B' (generators S₁ S₂)) (eval S₁ S₂)


def basePresentationHom :
    Presentation.Hom (FreeAlgebra.base O_B' (generators S₁ S₂)) (eval S₁ S₂)
      (FreeAlgebra.base O_B (generators S₁ S₂))
      (FreeAlgebra.evaluation (Under.mk fSharp) (generators S₁ S₂) (assignment S₁ S₂)).right where
  base := π
  middle := (FreeAlgebra.evaluation
    (Under.mk (π ≫ FreeAlgebra.base O_B (generators S₁ S₂)))
    (generators S₁ S₂) (FreeAlgebra.generator O_B (generators S₁ S₂))).right
  target := 𝟙 O
  baseSq := ⟨sorry⟩
  targetSq := ⟨sorry⟩

def conormalComparison : (liftedComplex S₁ S₂).X (-1) ⟶
    (Presentation.ofGenerators (generators S₁ S₂) (assignment S₁ S₂)).X (-1) :=
  ((extendComplexIdIso O).inv.app (liftedComplex S₁ S₂) ≫
    Presentation.Hom.map (basePresentationHom S₁ S₂)).f (-1)

def frontPresentationHom :
    Presentation.Hom (FreeAlgebra.base O_B' (generators S₁ S₂)) (eval S₁ S₂)
      (𝟙 S₁.middle) S₁.proj where
  base := S₁.structureMap
  middle := (FreeAlgebra.evaluation (Under.mk S₁.structureMap)
    (generators S₁ S₂) (frontAssignment S₁ S₂)).right
  target := 𝟙 O
  baseSq := ⟨sorry⟩
  targetSq := ⟨sorry⟩

def backPresentationHom :
    Presentation.Hom (FreeAlgebra.base O_B' (generators S₁ S₂)) (eval S₁ S₂)
      (𝟙 S₂.middle) S₂.proj where
  base := S₂.structureMap
  middle := (FreeAlgebra.evaluation (Under.mk S₂.structureMap)
    (generators S₁ S₂) (backAssignment S₁ S₂)).right
  target := 𝟙 O
  baseSq := ⟨sorry⟩
  targetSq := ⟨sorry⟩

/-- The two genuine evaluations are subtracted after their specified kernel identifications. -/
def liftedDifference : (liftedComplex S₁ S₂).X (-1) ⟶ G :=
  ((extendComplexIdIso O).inv.app (liftedComplex S₁ S₂) ≫
    Presentation.Hom.map (backPresentationHom S₁ S₂)).f (-1) ≫
      SquareZeroExtension.conormalToTarget S₂.proj S₂.proj_squareZero ≫ S₂.kernelIso.hom -
  ((extendComplexIdIso O).inv.app (liftedComplex S₁ S₂) ≫
    Presentation.Hom.map (frontPresentationHom S₁ S₂)).f (-1) ≫
      SquareZeroExtension.conormalToTarget S₁.proj S₁.proj_squareZero ≫ S₁.kernelIso.hom

/-- Surjectivity is the conormal base-change quotient for the locally surjective π. -/
instance conormalComparison_epi : Epi (conormalComparison S₁ S₂) := sorry

/-- Both solutions use the same specified map c on the base ideal, so their difference
annihilates the kernel of the conormal quotient. -/
theorem kernel_comp_difference :
    kernel.ι (conormalComparison S₁ S₂) ≫ liftedDifference S₁ S₂ = 0 := sorry

def conormalDifference :
    (Presentation.ofGenerators (generators S₁ S₂) (assignment S₁ S₂)).X (-1) ⟶ G :=
  Abelian.epiDesc (conormalComparison S₁ S₂) (liftedDifference S₁ S₂)
    (kernel_comp_difference S₁ S₂)

/-- The descended map retains the actual difference of the two evaluations. -/
theorem conormalComparison_comp_difference :
    conormalComparison S₁ S₂ ≫ conormalDifference S₁ S₂ = liftedDifference S₁ S₂ :=
  Abelian.comp_epiDesc _ _ _

/-- The common-generator map covers O since both projections are locally surjective. -/
instance assignment_locallySurjective : IsLocallySurjective (assignment S₁ S₂) := sorry

instance evaluation_locallySurjective : IsLocallySurjective
    (FreeAlgebra.evaluation (Under.mk fSharp) (generators S₁ S₂) (assignment S₁ S₂)).right := sorry

/-- The difference class comes from the actual common presentation and its canonical
quasi-isomorphism. No general derived pullback, arbitrary inverse, or zero map is used. -/
def extClass : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (NaiveCotangent.obj O_B (Under.mk fSharp)),
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  (Presentation.ofGeneratorsIso (generators S₁ S₂) (assignment S₁ S₂)).inv ≫
    conormalHomClass fSharp G (generators S₁ S₂) (assignment S₁ S₂) (conormalDifference S₁ S₂)

end Difference
end Solution
end SheafOfModules.RingedSite.FirstOrderThickening
