module

public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.Over.Abelian
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-below derived functors on slice sites

For a change of slice base, inverse image is exact and direct image is represented by the
canonical bounded-below total right-derived functor.  The entire API is a specialization of
`CategoryTheory.Adjunction.Derived.Plus`; no topology-comparison data is involved.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.Derived.Over

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y)
variable [HasInjectiveResolutions
  (Sheaf (J.over X) AddCommGrpCat.{max u v})]
variable [∀ P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v},
  (Over.map f).op.HasPointwiseRightKanExtension P]

/-- The degree-`i` direct image on abelian sheaves over slice sites.  The cocontinuous
presentation avoids choosing pullbacks along `f`; it is the same presentation used by the
bounded-below owner `Plus.pushforward`. -/
@[stacks 01E5 "degreewise direct image on slice sites"]
noncomputable abbrev pushforwardDegree (i : ℕ) :
    Sheaf (J.over X) AddCommGrpCat.{max u v} ⥤
      Sheaf (J.over Y) AddCommGrpCat.{max u v} :=
  ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
    (J.over X) (J.over Y)).rightDerived i

section ContinuousPresentation

/-- The degree-`i` direct image using the continuous pullback presentation.  Its ambient
`HasPullbacksAlong f` instance records the geometric input, while `pushforwardDegree` keeps the
cocontinuous presentation available when pointwise right Kan extensions are the preferred input.
Use `pushforwardDegreeContinuousOf` when the pullback certificate is supplied explicitly. -/
@[stacks 01E5 "continuous presentation of degreewise slice direct image"]
noncomputable abbrev pushforwardDegreeContinuous (i : ℕ) [HasPullbacksAlong f] :
    Sheaf (J.over X) AddCommGrpCat.{max u v} ⥤
      Sheaf (J.over Y) AddCommGrpCat.{max u v} :=
  (J.overMapPushforward AddCommGrpCat.{max u v} f).rightDerived i

/-- Explicit-bridge form of `pushforwardDegreeContinuous`, for a geometric certificate supplied
by a morphism property rather than registered as an instance. -/
@[stacks 01E5 "explicit continuous degreewise direct-image bridge"]
noncomputable def pushforwardDegreeContinuousOf (i : ℕ) (hp : HasPullbacksAlong f) :
    Sheaf (J.over X) AddCommGrpCat.{max u v} ⥤
      Sheaf (J.over Y) AddCommGrpCat.{max u v} :=
  letI : HasPullbacksAlong f := hp
  pushforwardDegreeContinuous J f i

/-- The canonical comparison between the continuous and cocontinuous degreewise direct-image
presentations. -/
@[stacks 01E5 "continuous-cocontinuous degreewise presentation bridge"]
noncomputable def pushforwardDegreePresentationIso
    (i : ℕ) [HasPullbacksAlong f] :
    pushforwardDegreeContinuous J f i ≅ pushforwardDegree J f i :=
  CategoryTheory.NatIso.rightDerived
    (J.overMapPushforwardIsoCocontinuous AddCommGrpCat.{max u v} f) i

/-- Explicit-bridge form of `pushforwardDegreePresentationIso`. -/
@[stacks 01E5 "explicit continuous-cocontinuous degreewise bridge"]
noncomputable def pushforwardDegreePresentationIsoOf
    (i : ℕ) (hp : HasPullbacksAlong f) :
    pushforwardDegreeContinuousOf J f i hp ≅ pushforwardDegree J f i :=
  letI : HasPullbacksAlong f := hp
  pushforwardDegreePresentationIso J f i

end ContinuousPresentation

end CategoryTheory.GrothendieckTopology.Derived.Over

namespace CategoryTheory.GrothendieckTopology.Derived.Over.Plus

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y)
variable [HasSheafify (J.over X) AddCommGrpCat.{max u v}]
variable [HasSheafify (J.over Y) AddCommGrpCat.{max u v}]
variable [∀ P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v},
  (Over.map f).op.HasPointwiseRightKanExtension P]

/-- The exact bounded-below derived inverse image along a change of slice base. -/
@[stacks 0EZF "bounded-below slice inverse image"]
noncomputable abbrev pullback :
    DerivedCategory.Plus (Sheaf (J.over Y) AddCommGrpCat.{max u v}) ⥤
      DerivedCategory.Plus (Sheaf (J.over X) AddCommGrpCat.{max u v}) :=
  Adjunction.Derived.Plus.left (J.overMapPullbackExact f)

section RightDerived

variable [Functor.HasRightDerivedFunctor
  (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
    (J.over X) (J.over Y)).toBoundedBelowDerived)
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (J.over X) AddCommGrpCat.{max u v}))]

/-- The canonical bounded-below derived direct image along a change of slice base. -/
@[stacks 0EZF "bounded-below slice direct image"]
noncomputable abbrev pushforward :
    DerivedCategory.Plus (Sheaf (J.over X) AddCommGrpCat.{max u v}) ⥤
      DerivedCategory.Plus (Sheaf (J.over Y) AddCommGrpCat.{max u v}) :=
  Adjunction.Derived.Plus.right
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (J.over X) (J.over Y))

/-- The localization factor of bounded-below slice inverse image. -/
@[stacks 0EZF "bounded-below slice inverse-image factor"]
noncomputable abbrev pullbackFactor :
    DerivedCategory.Plus.Qh ⋙ pullback J f ⟶
      (J.overMapPullback AddCommGrpCat.{max u v} f).toBoundedBelowDerived :=
  Adjunction.Derived.Plus.leftFactor (J.overMapPullbackExact f)

/-- The localization unit of bounded-below slice direct image. -/
@[stacks 0EZF "bounded-below slice direct-image unit"]
noncomputable abbrev pushforwardUnit :
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (J.over X) (J.over Y)).toBoundedBelowDerived ⟶
      DerivedCategory.Plus.Qh ⋙ pushforward J f :=
  Adjunction.Derived.Plus.rightUnit
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (J.over X) (J.over Y))

/-- The bounded-below derived inverse-image/direct-image adjunction on slice sites. -/
@[stacks 0EZF "bounded-below slice derived adjunction"]
noncomputable def adjunction :
    pullback J f ⊣ pushforward J f :=
  Adjunction.Derived.Plus.adjunction
    (J.overMapPullbackExact f)
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (J.over X) (J.over Y))
    (J.overMapCocontinuousAdjunction AddCommGrpCat.{max u v} f)

end RightDerived

end CategoryTheory.GrothendieckTopology.Derived.Over.Plus
