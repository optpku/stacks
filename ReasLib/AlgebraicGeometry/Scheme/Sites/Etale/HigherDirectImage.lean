/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Comparison
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.HigherDirectImage
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Higher direct images on small étale sites
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Every abelian sheaf on a small étale site admits an injective resolution. -/
instance abelianSheaf_hasInjectiveResolutions {X : Scheme.{u}}
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}] :
    HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) := sorry

/-- The small étale pushforward preserves injective abelian sheaves. -/
instance smallEtalePushforward_preservesInjectiveObjects {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}] :
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology).PreservesInjectiveObjects := sorry

/-- The pushforward of sheaves along a composition of scheme morphisms is identified with
the pushforward along the composite site morphism. -/
def schemePushforwardCompIso {T U V : Scheme.{u}}
    {f : V ⟶ U} {g : U ⟶ T} {h : V ⟶ T}
    (e : smallEtalePullback g ⋙ smallEtalePullback f ≅ smallEtalePullback h) :
    @Functor.sheafPushforwardContinuous _ _ _ _ (smallEtalePullback f) AddCommGrpCat.{u} _
          U.smallEtaleTopology V.smallEtaleTopology
          (smallEtalePullback_isContinuous f) ⋙
        @Functor.sheafPushforwardContinuous _ _ _ _ (smallEtalePullback g) AddCommGrpCat.{u} _
          T.smallEtaleTopology U.smallEtaleTopology
          (smallEtalePullback_isContinuous g) ≅
      @Functor.sheafPushforwardContinuous _ _ _ _ (smallEtalePullback h) AddCommGrpCat.{u} _
        T.smallEtaleTopology V.smallEtaleTopology
        (smallEtalePullback_isContinuous h) :=
  Functor.sheafPushforwardContinuousComp' e AddCommGrpCat.{u}
    T.smallEtaleTopology U.smallEtaleTopology V.smallEtaleTopology

/-- Higher direct image along a scheme morphism, with the source and target étale sites fixed. -/
def schemeHigherDirectImage {T U : Scheme.{u}} (f : U ⟶ T)
    [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
    (G : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) (degree : ℕ) :
    Sheaf T.smallEtaleTopology AddCommGrpCat.{u} :=
  @higherDirectImage _ _ _ _ U.smallEtaleTopology T.smallEtaleTopology
    (smallEtalePullback f) (smallEtalePullback_isContinuous f) _ _ _ G degree

/-- The map on higher direct images induced by a morphism of étale sheaves. -/
def schemeHigherDirectImageMap {T U : Scheme.{u}} (f : U ⟶ T)
    [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]
    {G G' : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}} (morphism : G ⟶ G') (degree : ℕ) :
    schemeHigherDirectImage f G degree ⟶ schemeHigherDirectImage f G' degree :=
  @higherDirectImageMap _ _ _ _ U.smallEtaleTopology T.smallEtaleTopology
    (smallEtalePullback f) (smallEtalePullback_isContinuous f) _ _ _ G G' morphism degree

end AlgebraicGeometry.Scheme.Etale

end
