/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import stacks_project.Chap63.Lemma_63_4_5

/-!
# Non-derived upper shriek for locally quasi-finite morphisms

The right adjoint `f^!` of compact-support `f_!` on abelian étale sheaves,
together with the skyscraper identification
`f^!(ȳ_* A) ≅ ∏_{f(x̄)=ȳ} x̄_* A`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Etale
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- Compact-support direct image `f_!` on abelian étale sheaves is a left
adjoint. -/
instance lowerShriek_isLeftAdjoint : (lowerShriek f).IsLeftAdjoint :=
  sorry

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

/-- The fibrewise product of abelian skyscraper sheaves at geometric points of
`X` over `ybar`. -/
def abelianSkyscraperProduct :
    AddCommGrpCat.{u} ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u} where
  obj A := ∏ᶜ fun x : Over f ybar ↦
    (toSmallEtalePoint x.toGeometricPoint).skyscraperSheafFunctor.obj A
  map {A B} φ := Limits.Pi.map fun x : Over f ybar ↦
    (toSmallEtalePoint x.toGeometricPoint).skyscraperSheafFunctor.map φ
  map_id := sorry
  map_comp := sorry

/-- Evaluating the fibrewise abelian skyscraper product recovers the product of
skyscrapers. -/
theorem abelianSkyscraperProduct_obj (A : AddCommGrpCat.{u}) :
    (abelianSkyscraperProduct f ybar).obj A =
      ∏ᶜ fun x : Over f ybar ↦
        (toSmallEtalePoint x.toGeometricPoint).skyscraperSheafFunctor.obj A :=
  sorry

/-- The skyscraper-product functor acts on a morphism of abelian groups by the
product of the induced skyscraper maps. -/
theorem abelianSkyscraperProduct_map {A B : AddCommGrpCat.{u}} (φ : A ⟶ B) :
    (abelianSkyscraperProduct f ybar).map φ =
      Limits.Pi.map fun x : Over f ybar ↦
        (toSmallEtalePoint x.toGeometricPoint).skyscraperSheafFunctor.map φ :=
  sorry

/-- The fibrewise coproduct of abelian stalks is left adjoint to the fibrewise
product of skyscrapers, via the product/coproduct and skyscraper
hom-equivalences. -/
def abelianStalkCoproductAdjunction :
    abelianStalkCoproduct f ybar ⊣ abelianSkyscraperProduct f ybar :=
  Adjunction.mkOfHomEquiv
    { homEquiv F A :=
        { toFun g :=
            Pi.lift fun x : Over f ybar ↦
              ((toSmallEtalePoint x.toGeometricPoint).skyscraperSheafAdjunction.homEquiv
                  F A)
                (Sigma.ι (fun y : Over f ybar ↦
                    (toSmallEtalePoint y.toGeometricPoint).sheafFiber.obj F) x ≫ g)
          invFun h :=
            Sigma.desc fun x : Over f ybar ↦
              ((toSmallEtalePoint x.toGeometricPoint).skyscraperSheafAdjunction.homEquiv
                  F A).symm
                (h ≫ Pi.π (fun y : Over f ybar ↦
                    (toSmallEtalePoint y.toGeometricPoint).skyscraperSheafFunctor.obj A) x)
          left_inv := sorry
          right_inv := sorry }
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- The hom-equivalence of `abelianStalkCoproductAdjunction`. -/
def abelianStalkCoproductAdjunction_homEquiv
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (A : AddCommGrpCat.{u}) :
    ((abelianStalkCoproduct f ybar).obj F ⟶ A) ≃
      (F ⟶ (abelianSkyscraperProduct f ybar).obj A) :=
  (abelianStalkCoproductAdjunction f ybar).homEquiv F A

variable [LocallyOfFiniteType f]

/-- `f^!` of a skyscraper at `ybar` is the product of fibre skyscrapers,
naturally in the abelian group. The extra `[LocallyOfFiniteType f]` is the
standing convention of Lemma 63.4.5 used to identify stalks of `f_!`; it is
not part of the owner `upperShriek`. -/
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
