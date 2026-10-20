module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Sections
import StacksCheckRecall

/-!
# Canonical maps from objectwise cotangent complexes

Remark 92.18.5 records the canonical map of complexes of `B(U)`-modules
`L(B(U)/A(U)) ⟶ L(φ)(U)`, its compatibility with restriction, and the
identification of `L(φ)` with the sheafification of `U ↦ L(B(U)/A(U))`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open Opposite
open SheafOfModules.RingedSite.CotangentComplex
open SheafOfModules.RingedSite

noncomputable section

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]

/- Remark 92.18.5. The canonical maps from section-ring cotangent complexes commute
with restriction, and the sheaf cotangent complex is their degreewise sheafification. -/
@[stacks 08SX]
#check (SheafOfModules.RingedSite.CotangentComplex.Sections.comparison_isIso :
  ∀ {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B),
    IsIso (SheafOfModules.RingedSite.CotangentComplex.Sections.comparison φ))

#check (SheafOfModules.RingedSite.CotangentComplex.Homology.sectionsComplexMap :
  ∀ {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (X : Cᵒᵖ),
    RingHom.cotangentComplex (φ.hom.app X).hom ⟶
      ((SheafOfModules.evaluation.{u} (ringSheaf J B) X).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ)))

#check (SheafOfModules.RingedSite.CotangentComplex.Sections.sectionsComplexMap_naturality :
  ∀ {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) {X Y : Cᵒᵖ} (f : X ⟶ Y),
    SheafOfModules.RingedSite.CotangentComplex.Homology.sectionsComplexMap φ X ≫
        SheafOfModules.RingedSite.CotangentComplex.Sections.evalRestrict φ f =
      SheafOfModules.RingedSite.CotangentComplex.Homology.complexMap φ f ≫
        ((ModuleCat.restrictScalars (B.obj.map f).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (SheafOfModules.RingedSite.CotangentComplex.Homology.sectionsComplexMap φ Y))
