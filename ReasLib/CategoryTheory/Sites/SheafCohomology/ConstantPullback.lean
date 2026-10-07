module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

noncomputable section

universe u v w r

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K]
    [HasSheafify J AddCommGrpCat.{max u v w}]
    [HasSheafify K AddCommGrpCat.{max u v w}]

/-- Inverse image of abelian sheaves along a continuous representably flat functor
preserves finite limits, with coefficients large enough for left Kan extensions. -/
instance sheafPullbackAbelian_preservesFiniteLimits [RepresentablyFlat F] :
    PreservesFiniteLimits
      (F.sheafPushforwardContinuous AddCommGrpCat.{max u v w} J K).leftAdjoint := sorry

/-- Inverse image identifies a constant abelian sheaf with the constant sheaf
of the same group when the site functor transports a terminal object. -/
def constantSheafPullbackIso {terminal : C} (h_terminal : IsTerminal terminal)
    (h_image : IsTerminal (F.obj terminal)) (A : AddCommGrpCat.{max u v w}) :
    (F.sheafPushforwardContinuous AddCommGrpCat.{max u v w} J K).leftAdjoint.obj
      ((constantSheaf J AddCommGrpCat.{max u v w}).obj A) ≅
      (constantSheaf K AddCommGrpCat.{max u v w}).obj A :=
  (((constantSheafAdj J AddCommGrpCat.{max u v w} h_terminal).comp
    (F.sheafAdjunctionContinuous AddCommGrpCat.{max u v w} J K)).leftAdjointUniq
      (constantSheafAdj K AddCommGrpCat.{max u v w} h_image)).app A

variable [RepresentablyFlat F]
    [HasExt.{r} (Sheaf J AddCommGrpCat.{max u v w})]
    [HasExt.{r} (Sheaf K AddCommGrpCat.{max u v w})]

/-- Pullback on constant-coefficient cohomology is induced by exact inverse image,
the inverse comparison of constant integer sheaves, and the coefficient comparison. -/
def constantCohomologyPullback {terminal : C} (h_terminal : IsTerminal terminal)
    (h_image : IsTerminal (F.obj terminal)) (A : AddCommGrpCat.{max u v w}) (q : ℕ) :
    (Sheaf.functorH J q).obj ((constantSheaf J AddCommGrpCat.{max u v w}).obj A) ⟶
      (Sheaf.functorH K q).obj ((constantSheaf K AddCommGrpCat.{max u v w}).obj A) :=
  let pull : Sheaf J AddCommGrpCat.{max u v w} ⥤ Sheaf K AddCommGrpCat.{max u v w} :=
    (F.sheafPushforwardContinuous AddCommGrpCat.{max u v w} J K).leftAdjoint
  let integers : Sheaf J AddCommGrpCat.{max u v w} :=
    (constantSheaf J AddCommGrpCat.{max u v w}).obj
    (AddCommGrpCat.of (ULift.{max u v w} ℤ))
  let targetIntegers : Sheaf K AddCommGrpCat.{max u v w} :=
    (constantSheaf K AddCommGrpCat.{max u v w}).obj
      (AddCommGrpCat.of (ULift.{max u v w} ℤ))
  let coefficients : Sheaf J AddCommGrpCat.{max u v w} :=
    (constantSheaf J AddCommGrpCat.{max u v w}).obj A
  let integerComparison : pull.obj integers ≅ targetIntegers :=
    F.constantSheafPullbackIso J K h_terminal h_image
    (AddCommGrpCat.of (ULift.{max u v w} ℤ))
  let coefficientComparison : pull.obj coefficients ≅
      (constantSheaf K AddCommGrpCat.{max u v w}).obj A :=
    F.constantSheafPullbackIso J K h_terminal h_image A
  let exactMap : Ext.{r} integers coefficients q →+
      Ext.{r} (pull.obj integers) (pull.obj coefficients) q :=
    Functor.mapExtAddHom.{r, r} pull integers coefficients q
  let integerClass : Ext.{r} targetIntegers (pull.obj integers) 0 :=
    Ext.mk₀ integerComparison.inv
  let integerMap := Ext.precomp integerClass (pull.obj coefficients) (zero_add q)
  AddCommGrpCat.ofHom exactMap ≫ AddCommGrpCat.ofHom integerMap ≫
    (Sheaf.functorH K q).map coefficientComparison.hom

/-- The pullback of a constant-coefficient cohomology class is its exact inverse-image
class precomposed with the integer comparison and postcomposed with the coefficient comparison. -/
theorem constantCohomologyPullback_apply {terminal : C} (h_terminal : IsTerminal terminal)
    (h_image : IsTerminal (F.obj terminal)) (A : AddCommGrpCat.{max u v w}) (q : ℕ)
    (x : ((constantSheaf J AddCommGrpCat.{max u v w}).obj A).H q) :
    (F.constantCohomologyPullback J K h_terminal h_image A q).hom x =
      Sheaf.H.map.{r} (F.constantSheafPullbackIso J K h_terminal h_image A).hom q
        ((Ext.mk₀.{r} (F.constantSheafPullbackIso J K h_terminal h_image
            (AddCommGrpCat.of (ULift.{max u v w} ℤ))).inv).comp
          (Functor.mapExtAddHom.{r, r}
            (F.sheafPushforwardContinuous AddCommGrpCat.{max u v w} J K).leftAdjoint
            ((constantSheaf J AddCommGrpCat.{max u v w}).obj
              (AddCommGrpCat.of (ULift.{max u v w} ℤ)))
            ((constantSheaf J AddCommGrpCat.{max u v w}).obj A) q x) (zero_add q)) := sorry

end CategoryTheory.Functor
