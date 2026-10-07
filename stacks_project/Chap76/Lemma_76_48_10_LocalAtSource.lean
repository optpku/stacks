module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap67.Lemma_67_36_4_Syntomic
public import stacks_project.Chap73.Definition_73_4_1_Precoverage
public import stacks_project.Chap76.Definition_76_48_1_LocalCompleteIntersection

/-!
# Syntomic source-locality of local complete intersection morphisms

Local complete intersection morphisms of algebraic spaces are local on the
source for the syntomic precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection

/-- Local complete intersection morphisms of algebraic spaces are local on the
source for the syntomic precoverage. -/
instance isLocalAtSourceSyntomic {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@IsLocalCompleteIntersection S : MorphismProperty (AlgebraicSpace S))
      (precoverage (@Syntomic S)) :=
  sorry

/-- A morphism of algebraic spaces is a local complete intersection if and only
if it remains so after precomposition with every member of a syntomic covering
of the source. -/
theorem iff_forall_comp {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (𝒰 : (precoverage (@Syntomic S)).ZeroHypercover X) :
    IsLocalCompleteIntersection f ↔ ∀ i, IsLocalCompleteIntersection (𝒰.f i ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection
