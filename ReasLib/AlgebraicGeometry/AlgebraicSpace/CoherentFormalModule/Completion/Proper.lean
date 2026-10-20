module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Completion.Existence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoherentCompletion

/-- Coherent completion along `I 𝒪_X` on a proper algebraic space over the
spectrum of an `I`-adically complete Noetherian ring is an equivalence of categories. -/
instance functor_isEquivalence_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))} [Proper (SchemeRealization.toBase X)] :
    (functor (pullbackIdeal I (SchemeRealization.toBase X))).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace.CoherentCompletion
