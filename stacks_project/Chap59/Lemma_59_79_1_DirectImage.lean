/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import ReasLib.CategoryTheory.Adjunction.Abelian
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionsWithSupport

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The direct-image functor on abelian sheaves induced by the small étale pullback along a scheme
morphism. -/
noncomputable abbrev etaleDirectImage {X Z : Scheme.{u}} (i : Z ⟶ X) :
    Sheaf Z.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (Scheme.smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
    X.smallEtaleTopology Z.smallEtaleTopology

/- Exactness of the small étale direct-image functor for a closed immersion. -/
#check (AlgebraicGeometry.Scheme.Etale.directImage_exact_of_isClosedImmersion :
  ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
    exactFunctor
      (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      ((Scheme.smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology))

end AlgebraicGeometry
