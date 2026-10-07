module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

/-- A family of scheme morphisms is a standard covering when it jointly covers
the target and each member is an open immersion, étale, smooth, syntomic, or
flat of finite presentation, according to the selected topology. -/
def StandardCovering {T : Scheme.{u}} (τ : StandardTopology)
    {ι : Type v} (X : ι → Scheme.{u}) (f : ∀ i, X i ⟶ T) : Prop :=
  (∀ x : T, ∃ i, x ∈ Set.range (f i)) ∧
    ∀ i,
      match τ with
      | .zariski => IsOpenImmersion (f i)
      | .etale => Etale (f i)
      | .smooth => Smooth (f i)
      | .syntomic => Syntomic (f i)
      | .fppf => Flat (f i) ∧ Scheme.Hom.FinitePresentation (f i)

/-- A standard covering is precisely a jointly surjective family whose members
satisfy the morphism property selected by the topology. -/
theorem standardCovering_iff {T : Scheme.{u}} (τ : StandardTopology)
    {ι : Type v} (X : ι → Scheme.{u}) (f : ∀ i, X i ⟶ T) :
    StandardCovering τ X f ↔
      (∀ x : T, ∃ i, x ∈ Set.range (f i)) ∧
        ∀ i,
          match τ with
          | .zariski => IsOpenImmersion (f i)
          | .etale => Etale (f i)
          | .smooth => Smooth (f i)
          | .syntomic => Syntomic (f i)
          | .fppf => Flat (f i) ∧ Scheme.Hom.FinitePresentation (f i) := sorry

end AlgebraicGeometry.Scheme
