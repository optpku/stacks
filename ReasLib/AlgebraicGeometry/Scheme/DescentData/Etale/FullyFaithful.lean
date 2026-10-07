module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale.Faithful
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Submersive
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor

/-- Pullback to singleton étale descent data along a submersive scheme morphism is fully
faithful when every étale base change of the morphism is submersive. -/
@[stacks 0BTK]
theorem fullyFaithful_of_submersive_etaleBaseChange
    {X S : Scheme.{u}} (f : X ⟶ S) [Submersive f]
    (h_baseChange : ∀ U : S.Etale, Submersive (pullback.snd f U.hom)) :
    Nonempty (canonicalFunctor f).FullyFaithful := sorry

/-- Pullback along a surjective universally closed scheme morphism is fully faithful on
étale descent data. -/
@[stacks 0BTL]
theorem fullyFaithful_of_surjective_universallyClosed
    {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f] [UniversallyClosed f] :
    Nonempty (canonicalFunctor f).FullyFaithful := sorry

/-- Pullback along a surjective universally open scheme morphism is fully faithful on
étale descent data. -/
@[stacks 0BTL]
theorem fullyFaithful_of_surjective_universallyOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f] [UniversallyOpen f] :
    Nonempty (canonicalFunctor f).FullyFaithful := sorry

/-- Pullback along a surjective quasi-compact flat scheme morphism is fully faithful on
étale descent data. -/
@[stacks 0BTL]
theorem fullyFaithful_of_surjective_quasiCompact_flat
    {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f] [QuasiCompact f] [Flat f] :
    Nonempty (canonicalFunctor f).FullyFaithful := sorry

end AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor
