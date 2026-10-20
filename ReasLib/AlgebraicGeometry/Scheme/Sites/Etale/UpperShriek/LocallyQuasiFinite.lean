module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.SkyscraperProduct

/-!
# Non-derived upper shriek for locally quasi-finite morphisms

The right adjoint of compact-support direct image on abelian étale sheaves,
together with its fibrewise skyscraper formula.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [LocallyQuasiFinite f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- Compact-support direct image `f_!` on abelian étale sheaves is a left
adjoint. -/
instance lowerShriek_isLeftAdjoint [LocallyOfFiniteType f] : (lowerShriek f).IsLeftAdjoint :=
  sorry

variable [LocallyOfFiniteType f]

/-- The non-derived upper shriek `f^!` on abelian étale sheaves, the chosen
right adjoint of `lowerShriek`. -/
def upperShriek :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (lowerShriek f).rightAdjoint

/-- `upperShriek f` is the chosen right adjoint of `lowerShriek f`. -/
theorem upperShriek_def :
    upperShriek f = (lowerShriek f).rightAdjoint :=
  sorry

/-- The adjunction `f_! ⊣ f^!` on abelian étale sheaves. -/
def lowerShriekAdjunction : lowerShriek f ⊣ upperShriek f :=
  Adjunction.ofIsLeftAdjoint (lowerShriek f)

/-- The hom-equivalence of the abelian compact-support adjunction. -/
def lowerShriekAdjunction_homEquiv
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    ((lowerShriek f).obj F ⟶ G) ≃ (F ⟶ (upperShriek f).obj G) :=
  (lowerShriekAdjunction f).homEquiv F G

variable (ybar : GeometricPoint Y)
variable [HasProducts.{u} AddCommGrpCat.{u}]

/-- `f^!` of a skyscraper at `ybar` is the product of fibre skyscrapers,
naturally in the abelian group. -/
def upperShriekSkyscraperIso :
    (toSmallEtalePoint ybar).skyscraperSheafFunctor ⋙ upperShriek f ≅
      abelianSkyscraperProduct f ybar :=
  conjugateIsoEquiv
    ((lowerShriekAdjunction f).comp
      (toSmallEtalePoint ybar).skyscraperSheafAdjunction)
    (abelianStalkCoproductAdjunction f ybar)
    (lowerShriekStalkIso f ybar).symm

/-- The skyscraper identification of `upperShriek`, evaluated at an abelian
group. -/
def upperShriekSkyscraperIso_app (A : AddCommGrpCat.{u}) :
    (upperShriek f).obj
        ((toSmallEtalePoint ybar).skyscraperSheafFunctor.obj A) ≅
      (abelianSkyscraperProduct f ybar).obj A :=
  (upperShriekSkyscraperIso f ybar).app A

end AlgebraicGeometry.Scheme.Etale

end
