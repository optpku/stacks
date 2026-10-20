module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyEtale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale

/-!
# Formal étaleness via étale scheme squares

A morphism of algebraic spaces is formally étale if and only if its induced
morphism is formally étale on étale scheme charts, and if and only if this
holds on one square with surjective charts.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormallyEtale

/-- There is a commutative square of schemes over `f` with étale surjective
vertical charts and formally étale top arrow. -/
def existsSurjectiveEtaleSchemeSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (ψ : U ⟶ V),
    MorphismProperty.presheaf (MorphismProperty.over (@AlgebraicGeometry.Etale)) a ∧
      MorphismProperty.presheaf (MorphismProperty.over (@AlgebraicGeometry.Etale)) b ∧
        Function.Surjective (Points.map a) ∧ Function.Surjective (Points.map b) ∧
          CommSq (ofOverMap ψ) a b f ∧ AlgebraicGeometry.FormallyEtale ψ.left

/-- The existential étale-square predicate is equivalent to its expanded
quantified specification. -/
theorem existsSurjectiveEtaleSchemeSquare_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    existsSurjectiveEtaleSchemeSquare f ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (ψ : U ⟶ V),
        MorphismProperty.presheaf (MorphismProperty.over (@AlgebraicGeometry.Etale)) a ∧
          MorphismProperty.presheaf (MorphismProperty.over (@AlgebraicGeometry.Etale)) b ∧
            Function.Surjective (Points.map a) ∧ Function.Surjective (Points.map b) ∧
              CommSq (ofOverMap ψ) a b f ∧ AlgebraicGeometry.FormallyEtale ψ.left := sorry

/-- Formal étaleness of an algebraic-space morphism is equivalent to formal
étaleness étale locally on scheme charts. -/
theorem iff_etaleLocal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    FormallyEtale f ↔ AlgebraicSpace.etaleLocal @AlgebraicGeometry.FormallyEtale f := sorry

/-- Formal étaleness of an algebraic-space morphism is equivalent to the
existence of a surjective étale scheme square with formally étale top arrow. -/
theorem iff_existsSurjectiveEtaleSchemeSquare {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    FormallyEtale f ↔ existsSurjectiveEtaleSchemeSquare f := sorry

end AlgebraicGeometry.AlgebraicSpace.FormallyEtale
