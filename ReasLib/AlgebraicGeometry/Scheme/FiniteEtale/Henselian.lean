module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a proper scheme over a henselian local ring, restriction to the closed
fibre induces an equivalence on finite étale schemes. -/
instance finiteEtaleBaseChangeIsEquivalence
    {A : Type u} [CommRing A] [HenselianLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] :
    Functor.IsEquivalence
      (Scheme.finiteEtaleBaseChange (f.fiberι (IsLocalRing.closedPoint A))) := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

/-- For a henselian pair `(A, I)`, pullback along the quotient-induced spectrum
morphism is an equivalence on finite étale schemes. -/
instance finiteEtaleBaseChangeIsEquivalenceOfHenselianPair
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I] :
    Functor.IsEquivalence
      (Scheme.finiteEtaleBaseChange
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) := sorry

end AlgebraicGeometry.Scheme
