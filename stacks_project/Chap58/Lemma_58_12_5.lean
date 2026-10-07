module

public import ReasLib.FieldTheory.Galois.IntegralClosure.IndEtale
import StacksCheckRecall

@[expose] public section

universe u v w

namespace integralClosure.FixedPoints

/- Lemma 58.12.5: for a normal domain `A`, a (possibly infinite) Galois extension `L / K`
and a prime `q` of the integral closure, the localization of the inertia-fixed subalgebra at
the contracted prime is a filtered colimit of etale `A`-algebras. -/
@[stacks 0BSU] #check
  (integralClosure.FixedPoints.indEtale_localization_inertia :
    ∀ {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type w} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsGalois K L] (q : Ideal (integralClosure A L)) [q.IsPrime],
      RingHom.IndEtale
        (algebraMap A
          (Localization.AtPrime
            (q.under
              (FixedPoints.subalgebra A (integralClosure A L)
                (q.inertia Gal(L / K)))))))

end integralClosure.FixedPoints
