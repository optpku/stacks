module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import ReasLib.AlgebraicGeometry.Scheme.Spec.IdealSubobject
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a proper scheme over a henselian pair `(A, I)`, restriction to the
special fibre over `A ⧸ I` induces an equivalence on finite étale schemes. -/
instance finiteEtaleBaseChangeIsEquivalenceOfHenselianPair
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] :
    Functor.IsEquivalence
      (Scheme.finiteEtaleBaseChange (pullback.fst f (Spec.quotientMap I))) := sorry

end AlgebraicGeometry.Scheme.Hom
