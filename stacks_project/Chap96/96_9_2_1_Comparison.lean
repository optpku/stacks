/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Core
public import stacks_project.Chap96.«96_9_2_1_Restriction»

/-!
# Comparison morphism along a morphism of a groupoid fibration

A morphism `φ : x ⟶ y` of a category fibred in groupoids, lying over `a : U ⟶ V`,
induces a comparison morphism of small étale presheaves
`F|_{V_étale} ⟶ a_small,*(F|_{U_étale})`, whose component on an étale
neighborhood `V' → V` is `F(φ')` for the unique lift `φ' : x' ⟶ y'` of the
pullback square `U' = V' ×_V U`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry.Scheme Opposite

noncomputable section

universe u a b

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- Triangle identity for the base-change projection `U' ⟶ V'` in `Over S`. -/
theorem comparisonPushOverHom_w {x y : X.total} (φ : x ⟶ y)
    (V' : (X.p.obj y).left.Etale) :
    pullback.fst V'.hom (X.p.map φ).left ≫ (V'.hom ≫ (X.p.obj y).hom) =
      ((smallEtalePullback (X.p.map φ).left).obj V').hom ≫ (X.p.obj x).hom :=
  sorry

/-- The morphism `U' ⟶ V'` in `Over S` associated to the pullback square
`U' = V' ×_V U`. -/
def comparisonPushOverHom {x y : X.total} (φ : x ⟶ y)
    (V' : (X.p.obj y).left.Etale) :
    Over.mk (((smallEtalePullback (X.p.map φ).left).obj V').hom ≫ (X.p.obj x).hom) ⟶
      Over.mk (V'.hom ≫ (X.p.obj y).hom) :=
  Over.homMk (pullback.fst V'.hom (X.p.map φ).left) (comparisonPushOverHom_w φ V')

/-- The selected cartesian lift of `x` along an étale neighborhood, as a morphism
of the total category. -/
abbrev smallEtaleEval_toBase (x : X.total) (V' : (X.p.obj x).left.Etale) :
    (smallEtaleEval x).obj V' ⟶ x :=
  Chosen.cartesianHom X.p (etaleOver x V').hom ⟨x, rfl⟩

/-- The selected cartesian lift `smallEtaleEval_toBase` is strongly cartesian over
the corresponding morphism of `Over S`. -/
instance smallEtaleEval_toBase.isStronglyCartesian {x : X.total}
    {V' : (X.p.obj x).left.Etale} :
    X.p.IsStronglyCartesian (etaleOver x V').hom (smallEtaleEval_toBase x V') :=
  sorry

/-- The two paths around the comparison square agree in `Over S`. -/
theorem comparisonPushOver_comp {x y : X.total} (φ : x ⟶ y)
    (V' : (X.p.obj y).left.Etale) :
    (etaleOver x ((smallEtalePullback (X.p.map φ).left).obj V')).hom ≫ X.p.map φ =
      comparisonPushOverHom φ V' ≫ (etaleOver y V').hom :=
  sorry

/-- The composite `smallEtaleEval_toBase x U' ≫ φ` lifts
`(etaleOver x U').hom ≫ X.p.map φ`. -/
instance comparisonPushHom_isHomLift {x y : X.total} {φ : x ⟶ y}
    {V' : (X.p.obj y).left.Etale} :
    X.p.IsHomLift
      ((etaleOver x ((smallEtalePullback (X.p.map φ).left).obj V')).hom ≫ X.p.map φ)
      (smallEtaleEval_toBase x ((smallEtalePullback (X.p.map φ).left).obj V') ≫ φ) :=
  sorry

/-- The unique morphism `φ' : x' ⟶ y'` in `X` lifting the pullback square
`U' = V' ×_V U` against `φ : x ⟶ y`. -/
def comparisonPushHom {x y : X.total} (φ : x ⟶ y)
    (V' : (X.p.obj y).left.Etale) :
    (smallEtaleEval x).obj ((smallEtalePullback (X.p.map φ).left).obj V') ⟶
      (smallEtaleEval y).obj V' :=
  IsStronglyCartesian.map (p := X.p) (etaleOver y V').hom
    (smallEtaleEval_toBase y V') (comparisonPushOver_comp φ V')
    (smallEtaleEval_toBase x ((smallEtalePullback (X.p.map φ).left).obj V') ≫ φ)

/-- Comparison morphism `c_φ : F|_{V_étale} ⟶ a_small,*(F|_{U_étale})` associated
to `φ : x ⟶ y`, with component `F(φ')` on an étale neighborhood of `V`. -/
def comparisonPush {A : Type a} [Category.{b} A] {x y : X.total} (φ : x ⟶ y)
    (F : X.totalᵒᵖ ⥤ A) :
    restrictSmallEtale y F ⟶
      (smallEtalePullback (X.p.map φ).left).op ⋙ restrictSmallEtale x F where
  app V' := F.map (op (comparisonPushHom φ (unop V')))
  naturality := sorry

/-- Sections of `comparisonPush` over `V'` are `F.map (op (comparisonPushHom φ V'))`. -/
theorem comparisonPush_app {A : Type a} [Category.{b} A] {x y : X.total}
    (φ : x ⟶ y) (F : X.totalᵒᵖ ⥤ A) (V' : (X.p.obj y).left.Etale) :
    (comparisonPush φ F).app (op V') = F.map (op (comparisonPushHom φ V')) :=
  sorry

/-- The comparison morphism `comparisonPush φ F` is natural in the presheaf `F`. -/
theorem comparisonPush_map {A : Type a} [Category.{b} A] {x y : X.total}
    (φ : x ⟶ y) {F G : X.totalᵒᵖ ⥤ A} (η : F ⟶ G) :
    comparisonPush φ F ≫
        whiskerLeft ((smallEtalePullback (X.p.map φ).left).op ⋙ (smallEtaleEval x).op) η =
      whiskerLeft (smallEtaleEval y).op η ≫ comparisonPush φ G :=
  sorry

end AlgebraicGeometry.GroupoidsOver
