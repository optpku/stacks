module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap63.Lemma_63_4_5
public import stacks_project.Chap63.Remark_63_4_6_Covariance_with_respect_to_open_embeddings_OpenImmersion

/-!
# Stalk comparisons for open-immersion covariance

The locally quasi-finite covariance maps of Remark 63.4.6 are compatible with
the stalk coproduct formulas of Lemmas 63.4.2 and 63.4.5.
-/

@[expose] public section

open CategoryTheory hiding Over
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable {X' X Y : Scheme.{u}} (j : X' ⟶ X) (f : X ⟶ Y) (ybar : GeometricPoint Y)

/-- A geometric point of `X'` over `ȳ` yields a geometric point of `X` over `ȳ`
by composing with the open immersion `j`. -/
def Over.openImmersion (x' : Over (j ≫ f) ybar) : Over f ybar :=
  Over.of f ybar (x'.toScheme ≫ j) sorry

/-- The image geometric point of `Over.openImmersion` is composition with `j`. -/
theorem Over.openImmersion_toScheme (x' : Over (j ≫ f) ybar) :
    (Over.openImmersion j f ybar x').toScheme = x'.toScheme ≫ j :=
  sorry

end AlgebraicGeometry.Scheme.GeometricPoint

namespace AlgebraicGeometry.Scheme.Etale

variable {X' X : Scheme.{u}} (j : X' ⟶ X) [Etale j]

/-- Sections of `F|_{X'}` on an étale `X'`-scheme agree with sections of `F` on
the same scheme viewed over `X`. -/
def etaleRestrictionSectionsIso (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (U : X'.Etale) :
    ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F).obj.obj (op U) ≅
      F.obj.obj (op ((etaleRestriction j).obj U)) :=
  (etaleRestriction j).sheafPushforwardContinuousObjObjIso AddCommGrpCat.{u} F U

variable {Y : Scheme.{u}} (f : X ⟶ Y)
variable [IsOpenImmersion j] [LocallyQuasiFinite f]
variable (ybar : GeometricPoint Y)

/-- A lift of a geometric point of `X'` over `ȳ` to an étale `X'`-scheme is the
same lift of the image point of `X` to the restricted étale `X`-scheme. -/
def restrictionFiberElement (x' : Over (j ≫ f) ybar) (U : X'.Etale)
    (φ : (toSmallEtalePoint x'.toGeometricPoint).fiber.obj U) :
    (toSmallEtalePoint (Over.openImmersion j f ybar x').toGeometricPoint).fiber.obj
      ((etaleRestriction j).obj U) :=
  (CategoryTheory.Over.homMk φ.left sorry :
    (toSmallEtalePoint (Over.openImmersion j f ybar x').toGeometricPoint).fiber.obj
      ((etaleRestriction j).obj U))

/-- Identification of the stalk of `F|_{X'}` at a geometric point of `X'` over
`ȳ` with the stalk of `F` at the image geometric point of `X`. -/
def restrictionSheafFiber (x' : Over (j ≫ f) ybar)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint x'.toGeometricPoint).sheafFiber.obj
        ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) ⟶
      (toSmallEtalePoint
          (Over.openImmersion j f ybar x').toGeometricPoint).sheafFiber.obj F :=
  (toSmallEtalePoint x'.toGeometricPoint).presheafFiberDesc
    (fun U φ ↦
      (etaleRestrictionSectionsIso j F U).hom ≫
        (toSmallEtalePoint (Over.openImmersion j f ybar x').toGeometricPoint).toPresheafFiber
          ((etaleRestriction j).obj U) (restrictionFiberElement j f ybar x' U φ) F.1)
    sorry

/-- Inclusion of fibrewise stalk coproducts along an open immersion of the
source, reindexing geometric points of `X'` over `ȳ` to geometric points of `X`
over `ȳ`. -/
def abelianStalkCoproductOpenImmersion :
    etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙ abelianStalkCoproduct (j ≫ f) ybar ⟶
      abelianStalkCoproduct f ybar where
  app F :=
    Sigma.map' (Over.openImmersion j f ybar) fun x' ↦
      restrictionSheafFiber j f ybar x' F
  naturality := sorry

/-- Evaluating the fibre-coproduct covariance recovers `Sigma.map'` of the
stalk identifications. -/
theorem abelianStalkCoproductOpenImmersion_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (abelianStalkCoproductOpenImmersion j f ybar).app F =
      Sigma.map' (Over.openImmersion j f ybar) fun x' ↦
        restrictionSheafFiber j f ybar x' F :=
  sorry

variable [LocallyOfFiniteType f]

/-- Compatibility of the presheaf covariance with the stalk identifications of
Lemma 63.4.2. -/
theorem lowerShriekPresheafOpenImmersion_stalk
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    CommSq
      ((toSmallEtalePoint ybar).presheafFiber.map
        ((lowerShriekPresheafOpenImmersion j f).app F))
      ((lowerShriekPresheafStalkIso (j ≫ f) ybar).hom.app
        ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F))
      ((lowerShriekPresheafStalkIso f ybar).hom.app F)
      ((abelianStalkCoproductOpenImmersion j f ybar).app F) :=
  sorry

variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- Compatibility of the sheaf covariance with the stalk identifications of
Lemma 63.4.5. -/
theorem lowerShriekOpenImmersion_stalk
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    CommSq
      ((toSmallEtalePoint ybar).sheafFiber.map
        ((lowerShriekOpenImmersion j f).app F))
      ((lowerShriekStalkIso (j ≫ f) ybar).hom.app
        ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F))
      ((lowerShriekStalkIso f ybar).hom.app F)
      ((abelianStalkCoproductOpenImmersion j f ybar).app F) :=
  sorry


end AlgebraicGeometry.Scheme.Etale

end
