module

public import ReasLib.RingTheory.RingHom.SquareZero.Presentation

universe u

/- Polynomial lift compatibility bridge. -/
#check (RingHom.SquareZeroExtension.presentationLift :
  ∀ {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    {ι : Type u}
    (G : Algebra.Generators A B ι)
    (S : @RingHom.SquareZeroExtension.Solution A A _ _ B _ _ (RingHom.id A) _ N _ _ _
      (RingHom.SquareZeroExtension.zeroKernelMap A B N) _),
    letI := S.commRing
    letI : Algebra A S.carrier := S.fromA'.toAlgebra
    G.Ring →ₐ[A] S.carrier)
