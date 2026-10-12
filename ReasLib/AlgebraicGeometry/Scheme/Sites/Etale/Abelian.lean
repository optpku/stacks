/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Limits

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.Abelian

variable {A B C : Scheme.{u}}

/-- The direct image on abelian sheaves on small étale sites. -/
noncomputable abbrev directImage (a : A ⟶ B) :
    Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Scheme.smallEtalePullback a).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    B.smallEtaleTopology A.smallEtaleTopology

/-- The inverse image on abelian sheaves on small étale sites. -/
noncomputable abbrev inverseImage (a : A ⟶ B) :
    Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Scheme.smallEtalePullback a).sheafPullback AddCommGrpCat.{u + 1}
    B.smallEtaleTopology A.smallEtaleTopology

/-- The inverse image is left adjoint to the direct image on small étale sheaves. -/
noncomputable def adjunction (a : A ⟶ B) : inverseImage a ⊣ directImage a :=
  (Scheme.smallEtalePullback a).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    B.smallEtaleTopology A.smallEtaleTopology

/-- The direct image on abelian small étale sheaves is additive. -/
noncomputable instance directImage_additive (a : A ⟶ B) :
    (directImage a).Additive := sorry

/-- The inverse image on abelian small étale sheaves preserves finite limits. -/
noncomputable instance inverseImage_preservesFiniteLimits (a : A ⟶ B) :
    PreservesFiniteLimits (inverseImage a) := sorry

/-- The inverse image preserves finite colimits because it is a left adjoint. -/
noncomputable instance inverseImage_preservesFiniteColimits (a : A ⟶ B) :
    PreservesFiniteColimits (inverseImage a) :=
  @PreservesColimitsOfSize.preservesFiniteColimits _ _ _ _ (inverseImage a)
    (Adjunction.leftAdjoint_preservesColimits (adjunction a) :
      PreservesColimitsOfSize.{u + 1, u + 1} (inverseImage a))

/-- The inverse image on abelian small étale sheaves is exact. -/
noncomputable abbrev inverseImageExact (a : A ⟶ B) :
    Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (inverseImage a)

/-- Composition of direct images is canonically the direct image of a composite. -/
noncomputable def directImageCompIso (a : A ⟶ B) (b : B ⟶ C) :
    directImage a ⋙ directImage b ≅ directImage (a ≫ b) :=
  let siteIso : Scheme.smallEtalePullback b ⋙ Scheme.smallEtalePullback a ≅
      Scheme.smallEtalePullback (a ≫ b) :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) a b).symm
  Functor.sheafPushforwardContinuousComp' siteIso
    AddCommGrpCat.{u + 1} C.smallEtaleTopology B.smallEtaleTopology
      A.smallEtaleTopology

/-- Composition of inverse images is canonically the inverse image of a composite. -/
noncomputable def inverseImageCompIso (a : A ⟶ B) (b : B ⟶ C) :
    inverseImage (a ≫ b) ≅ inverseImage b ⋙ inverseImage a :=
  (Adjunction.leftAdjointCompIso (adjunction b) (adjunction a)
    (adjunction (a ≫ b)) (directImageCompIso a b)).symm

end AlgebraicGeometry.Scheme.Etale.Abelian

end
