/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.Sites.Derived.InverseImage
public import ReasLib.CategoryTheory.Sites.Over.Derived.Unbounded
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap84.«84_5_2_1_Site»
public import stacks_project.Chap84.Lemma_84_5_2_Relocalization

/-!
# Unbounded derived étale functors of algebraic spaces

This leaf names the unbounded derived restriction `i_g⁻¹`, the small étale
derived direct image `Rf_small,*`, and the big étale derived direct image
`Rf_big,*` used to compare cohomology on `(Spaces/Y)_étale` and `Y_étale`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.Derived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Derived restriction `i_g⁻¹` from `(Spaces/X)_étale` to the small étale site of `Y`. -/
noncomputable abbrev relocalization (g : Y ⟶ X)
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}] :
    DerivedCategory (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :=
  siteAbelianInverseImageDerived (smallEtaleTopology Y) (overEtaleTopology X)
    (relocalizationFunctor g)

/-- `relocalization g` is derived inverse image along étale relocalization. -/
theorem relocalization_eq (g : Y ⟶ X)
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}] :
    relocalization g =
      siteAbelianInverseImageDerived (smallEtaleTopology Y) (overEtaleTopology X)
        (relocalizationFunctor g) :=
  rfl

/-- The unbounded derived small étale direct image `Rf_small,*`. -/
noncomputable abbrev directImage (f : Y ⟶ X)
    [IsGrothendieckAbelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [(sheafPushforwardAbelian f).Additive] :
    DerivedCategory (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.KInjective.right (sheafPushforwardAbelian f)

/-- `directImage f` is the K-injective total right-derived functor of small étale
pushforward. -/
theorem directImage_eq (f : Y ⟶ X)
    [IsGrothendieckAbelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [(sheafPushforwardAbelian f).Additive] :
    directImage f = Adjunction.Derived.KInjective.right (sheafPushforwardAbelian f) :=
  rfl

/-- The unbounded derived big étale direct image `Rf_big,*` on slice sites. -/
noncomputable abbrev bigDirectImage (f : Y ⟶ X)
    [HasSheafify (overEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [∀ P : (Over Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P] :
    DerivedCategory (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  GrothendieckTopology.Derived.Over.pushforward
    (bigEtaleTopology : GrothendieckTopology (AlgebraicSpace S)) f

/-- `bigDirectImage f` is slice-site derived pushforward along `f` on the big étale
topology. -/
theorem bigDirectImage_eq (f : Y ⟶ X)
    [HasSheafify (overEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [∀ P : (Over Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P] :
    bigDirectImage f =
      GrothendieckTopology.Derived.Over.pushforward
        (bigEtaleTopology : GrothendieckTopology (AlgebraicSpace S)) f :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Etale.Derived

end
