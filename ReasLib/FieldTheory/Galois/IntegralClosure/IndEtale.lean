/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.FieldTheory.Galois.IntegralClosure.FixedPoints
public import ReasLib.RingTheory.Ideal.Inertia
public import ReasLib.RingTheory.Invariant.FixedPoints.Etale
public import ReasLib.RingTheory.RingHom.IndEtale.Colimit

@[expose] public section

universe u v w

namespace integralClosure.FixedPoints

/-- The localization of the inertia-fixed subalgebra of an integral closure is ind-etale over the
base domain. -/
theorem indEtale_localization_inertia
    {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type w} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsGalois K L]
    (q : Ideal (integralClosure A L)) [q.IsPrime] :
    RingHom.IndEtale
      (algebraMap A
        (Localization.AtPrime
          (q.under
            (FixedPoints.subalgebra A (integralClosure A L)
              (q.inertia Gal(L / K)))))) := sorry

end integralClosure.FixedPoints
