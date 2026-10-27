/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.MorphismOfSites.Exactness
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Relocalization

/-!
# Small-to-big étale derived adjunction of algebraic spaces

The morphism of topoi `π_X : Sh((Spaces/X)_étale) ⟶ Sh(X_étale)` is induced by
relocalization `smallEtaleSite X ⥤ Over X`. The abelian-sheaf
adjunction `π_X⁻¹ ⊣ π_{X,*}` induces an exact derived adjunction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

/-- Inverse image `π_X⁻¹` on abelian sheaves along identity-base étale
relocalization. -/
def etalePiInverseImage {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P] :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (relocalizationFunctor (𝟙 X)).sheafPullback AddCommGrpCat.{u + 1}
    (smallEtaleTopology X) (overEtaleTopology X)

/-- `π_X⁻¹` is sheaf pullback along identity-base étale relocalization. -/
theorem etalePiInverseImage_eq {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P] :
    etalePiInverseImage X =
      (relocalizationFunctor (𝟙 X)).sheafPullback AddCommGrpCat.{u + 1}
        (smallEtaleTopology X) (overEtaleTopology X) :=
  rfl

/-- Direct image `π_{X,*}` on abelian sheaves along identity-base étale
relocalization. -/
def etalePiPushforward {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (relocalizationFunctor (𝟙 X)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (smallEtaleTopology X) (overEtaleTopology X)

/-- `π_{X,*}` agrees with restriction `i_X⁻¹` along identity-base relocalization. -/
theorem etalePiPushforward_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    etalePiPushforward X = inverseImage (𝟙 X) :=
  rfl

/-- Inverse image `π_X⁻¹` preserves finite limits. -/
instance etalePiInverseImage_preservesFiniteLimits {S : Scheme.{u}}
    (X : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P] :
    PreservesFiniteLimits (etalePiInverseImage X) := sorry

/-- Inverse image `π_X⁻¹` preserves finite colimits. -/
instance etalePiInverseImage_preservesFiniteColimits {S : Scheme.{u}}
    (X : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P] :
    PreservesFiniteColimits (etalePiInverseImage X) := by
  letI : (etalePiInverseImage X).IsLeftAdjoint :=
    ((relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (overEtaleTopology X)).isLeftAdjoint
  infer_instance

/-- Direct image `π_{X,*}` preserves finite limits. -/
instance etalePiPushforward_preservesFiniteLimits {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    PreservesFiniteLimits (etalePiPushforward X) := by
  have : PreservesFiniteLimits
      (etalePiPushforward X ⋙ sheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :=
    inferInstanceAs (PreservesFiniteLimits
      (sheafToPresheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
          (relocalizationFunctor (𝟙 X)).op))
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})

/-- Direct image `π_{X,*}` preserves finite colimits. -/
instance etalePiPushforward_preservesFiniteColimits {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    PreservesFiniteColimits (etalePiPushforward X) := by
  letI : (etalePiPushforward X).IsLeftAdjoint :=
    ((relocalizationFunctor (𝟙 X)).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (overEtaleTopology X)).isLeftAdjoint
  infer_instance

/-- Inverse image `π_X⁻¹` is additive. -/
instance etalePiInverseImage_additive {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Preadditive (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P] :
    (etalePiInverseImage X).Additive := by
  letI : ((relocalizationFunctor (𝟙 X)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (overEtaleTopology X)).Additive :=
    show (etalePiPushforward X).Additive from
      Functor.additive_of_preserves_binary_products _
  exact ((relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (smallEtaleTopology X) (overEtaleTopology X)).left_adjoint_additive

/-- Direct image `π_{X,*}` is additive. -/
instance etalePiPushforward_additive {S : Scheme.{u}} (X : AlgebraicSpace S)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Preadditive (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})] :
    (etalePiPushforward X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Sheaf-level adjunction `π_X⁻¹ ⊣ π_{X,*}`. -/
def etalePiAdjunction {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P] :
    etalePiInverseImage X ⊣ etalePiPushforward X :=
  (relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (smallEtaleTopology X) (overEtaleTopology X)

/-- Derived adjunction of the exact functors `π_X⁻¹` and `π_{X,*}`. -/
def etalePiDerivedAdjunction {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P] :
    (etalePiInverseImage X).mapDerivedCategory ⊣
      (etalePiPushforward X).mapDerivedCategory :=
  Adjunction.mapDerivedCategory (etalePiAdjunction X)

/-- The sheaf-level adjunction unit of `π_X⁻¹ ⊣ π_{X,*}` is an isomorphism. -/
instance etalePiAdjunction_unit_isIso {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    IsIso ((etalePiAdjunction X).unit.app F) := by
  letI : (Over.map (𝟙 X)).Full := Functor.Full.of_iso (Over.mapId X).symm
  letI : (Over.map (𝟙 X)).Faithful := Functor.Faithful.of_iso (Over.mapId X).symm
  letI : (relocalizationFunctor (𝟙 X)).Full := inferInstance
  letI : (relocalizationFunctor (𝟙 X)).Faithful := inferInstance
  letI : (relocalizationFunctor (𝟙 X)).op.Full := inferInstance
  letI : (relocalizationFunctor (𝟙 X)).op.Faithful := inferInstance
  let adj := (relocalizationFunctor (𝟙 X)).sheafAdjunctionCocontinuous
    AddCommGrpCat.{u + 1} (smallEtaleTopology X) (overEtaleTopology X)
  haveI : ∀ G, IsIso (adj.counit.app G) := by
    intro G
    apply (isIso_iff_of_reflects_iso _
      (sheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})).mp
    change IsIso (((relocalizationFunctor (𝟙 X)).sheafAdjunctionCocontinuous
      AddCommGrpCat.{u + 1} (smallEtaleTopology X) (overEtaleTopology X)).counit.app G).hom
    rw [Functor.sheafAdjunctionCocontinuous_counit_app_hom]
    haveI : IsIso (((relocalizationFunctor (𝟙 X)).op.ranAdjunction
        AddCommGrpCat.{u + 1}).counit) :=
      Functor.reflective' (relocalizationFunctor (𝟙 X)).op
    exact NatIso.isIso_app_of_isIso _ G.obj
  haveI : IsIso adj.counit := NatIso.isIso_of_isIso_app _
  let triple : Adjunction.Triple (etalePiInverseImage X) (etalePiPushforward X)
      ((relocalizationFunctor (𝟙 X)).sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (smallEtaleTopology X) (overEtaleTopology X)) :=
    ⟨etalePiAdjunction X, adj⟩
  haveI : IsIso (etalePiAdjunction X).unit :=
    triple.isIso_unit_iff_isIso_counit.mpr (show IsIso adj.counit from inferInstance)
  infer_instance

/-- The unit of the derived small-to-big étale adjunction is an isomorphism. -/
instance etalePiDerivedAdjunction_unit_app_isIso {S : Scheme.{u}}
    (X : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P]
    (K : DerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIso ((etalePiDerivedAdjunction X).unit.app K) := by
  letI : Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :=
    Abelian.toPreadditive
  letI : Preadditive (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1}) :=
    Abelian.toPreadditive
  letI : HasZeroMorphisms (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :=
    Preadditive.preadditiveHasZeroMorphisms
  letI : HasZeroMorphisms (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1}) :=
    Preadditive.preadditiveHasZeroMorphisms
  rw [← NatTrans.isIso_app_iff_of_iso (etalePiDerivedAdjunction X).unit
    (DerivedCategory.Q.objObjPreimageIso K)]
  dsimp only [etalePiDerivedAdjunction, Adjunction.mapDerivedCategory]
  rw [Adjunction.localization_unit_app]
  let P : CochainComplex (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) ℤ :=
    DerivedCategory.Q.objPreimage K
  haveI : IsIso
      ((Adjunction.mapHomologicalComplexAdjunction (etalePiAdjunction X)
        (ComplexShape.up ℤ)).unit.app P) := by
    haveI : ∀ n, IsIso
        (((Adjunction.mapHomologicalComplexAdjunction (etalePiAdjunction X)
          (ComplexShape.up ℤ)).unit.app P).f n) := by
      intro n
      change IsIso (𝟙 (P.X n) ≫ (etalePiAdjunction X).unit.app (P.X n))
      simpa using etalePiAdjunction_unit_isIso X (P.X n)
    exact HomologicalComplex.Hom.isIso_of_components _
  change IsIso
    (DerivedCategory.Q.map
        ((Adjunction.mapHomologicalComplexAdjunction (etalePiAdjunction X)
          (ComplexShape.up ℤ)).unit.app P) ≫ _)
  haveI : IsIso (DerivedCategory.Q.map
      ((Adjunction.mapHomologicalComplexAdjunction (etalePiAdjunction X)
        (ComplexShape.up ℤ)).unit.app P)) := inferInstance
  apply IsIso.comp_isIso'
  · infer_instance
  · apply IsIso.comp_isIso'
    · exact NatIso.hom_app_isIso _ _
    · exact ((etalePiPushforward X).mapDerivedCategory.mapIso
        ((CatCommSq.iso
          ((etalePiInverseImage X).mapHomologicalComplex (ComplexShape.up ℤ))
          DerivedCategory.Q DerivedCategory.Q (etalePiInverseImage X).mapDerivedCategory).app
            P)).isIso_hom

/-- The derived small-to-big étale adjunction unit is invertible when the presheaf
left Kan extension along identity-base relocalization preserves finite limits. -/
theorem etalePiDerivedAdjunction_unit_isIso {S : Scheme.{u}}
    (X : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 X)).op.lan :
        ((smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
          ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}))]
    (K : DerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIso ((etalePiDerivedAdjunction X).unit.app K) :=
  etalePiDerivedAdjunction_unit_app_isIso X K

end AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
