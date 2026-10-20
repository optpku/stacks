/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
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
  sorry

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
  sorry

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
    PreservesFiniteColimits (etalePiInverseImage X) := sorry

/-- Direct image `π_{X,*}` preserves finite limits. -/
instance etalePiPushforward_preservesFiniteLimits {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    PreservesFiniteLimits (etalePiPushforward X) := sorry

/-- Direct image `π_{X,*}` preserves finite colimits. -/
instance etalePiPushforward_preservesFiniteColimits {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    PreservesFiniteColimits (etalePiPushforward X) := sorry

/-- Inverse image `π_X⁻¹` is additive. -/
instance etalePiInverseImage_additive {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Preadditive (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P] :
    (etalePiInverseImage X).Additive := sorry

/-- Direct image `π_{X,*}` is additive. -/
instance etalePiPushforward_additive {S : Scheme.{u}} (X : AlgebraicSpace S)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Preadditive (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})] :
    (etalePiPushforward X).Additive := sorry

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
    IsIso ((etalePiAdjunction X).unit.app F) := sorry

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
    IsIso ((etalePiDerivedAdjunction X).unit.app K) := sorry

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
