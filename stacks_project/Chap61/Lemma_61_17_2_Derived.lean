module

public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.Sites.Over.Derived.Unbounded
public import stacks_project.Chap61.Lemma_61_17_2_Pushforward

/-!
# Unbounded derived pro-étale pushforwards

K-injective total right-derived direct images `Rf_small,*` and `Rf_big,*` of
abelian sheaves on pro-étale sites.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {S T : Scheme.{u}} (f : T ⟶ S)

/-- Unbounded derived direct image `Rf_small,*` along the small pro-étale
morphism of `f`. -/
abbrev smallDerivedPushforward
    [IsGrothendieckAbelian (Sheaf (topology T) AddCommGrpCat.{u + 1})] :
    DerivedCategory (Sheaf (topology T) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (topology S) AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.KInjective.right (smallPushforward f)

/-- Derived small pro-étale direct image is the K-injective right-derived functor
of `smallPushforward`. -/
theorem smallDerivedPushforward_eq
    [IsGrothendieckAbelian (Sheaf (topology T) AddCommGrpCat.{u + 1})] :
    smallDerivedPushforward f =
      Adjunction.Derived.KInjective.right (smallPushforward f) := sorry

/-- Unbounded derived direct image `Rf_big,*` along the big pro-étale morphism of
`f`, presented by the cocontinuous slice-site owner. -/
abbrev bigDerivedPushforward
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over T) AddCommGrpCat.{u + 1}]
    [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P]
    [IsGrothendieckAbelian
      (Sheaf (proetaleTopology.over T) AddCommGrpCat.{u + 1})] :
    DerivedCategory (Sheaf (proetaleTopology.over T) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1}) :=
  Derived.Over.pushforward proetaleTopology f

/-- Derived big pro-étale direct image is unbounded derived slice-site
pushforward. -/
theorem bigDerivedPushforward_eq
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over T) AddCommGrpCat.{u + 1}]
    [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P]
    [IsGrothendieckAbelian
      (Sheaf (proetaleTopology.over T) AddCommGrpCat.{u + 1})] :
    bigDerivedPushforward f = Derived.Over.pushforward proetaleTopology f := sorry

end AlgebraicGeometry.Scheme.ProEt
