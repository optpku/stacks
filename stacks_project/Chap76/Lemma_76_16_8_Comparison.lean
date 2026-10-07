module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap76.Lemma_76_16_4_FormallyEtale

/-!
# Étale morphisms of algebraic spaces versus formal étaleness

A morphism of algebraic spaces is étale if and only if it is locally of finite
presentation and formally étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is étale if and only if it is locally of
finite presentation and formally étale. -/
theorem Etale.iff_locallyOfFinitePresentation_and_formallyEtale
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Etale f ↔ LocallyOfFinitePresentation f ∧ FormallyEtale f :=
  sorry

/-- An étale morphism of algebraic spaces is formally étale. -/
instance FormallyEtale.of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] : FormallyEtale f :=
  sorry

/-- A locally finitely presented, formally étale morphism of algebraic spaces is
étale. -/
instance Etale.of_locallyOfFinitePresentation_of_formallyEtale
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [FormallyEtale f] : Etale f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
