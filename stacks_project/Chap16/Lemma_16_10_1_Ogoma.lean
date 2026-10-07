module

import StacksCheckRecall
public import ReasLib.Algebra.Module.Torsion.Localization

@[expose] public section

universe u v

/- Lemma 16.10.1 (Ogoma): the source specialization concerns a finite module
over a Noetherian ring; the reusable owner only asks that the module itself be
Noetherian. -/
@[stacks 07FC] #check
  fun {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M]
    [IsNoetherianRing A] [Module.Finite A M]
    (S : Submonoid A) (π : A)
    (hlocal : Module.IsTorsionStable
      (Localization S) (LocalizedModule S M)
        (algebraMap A (Localization S) π)) ↦
      Module.IsTorsionStable.exists_denominator S π hlocal

#check @Module.IsTorsionStable.exists_denominator
#check @Module.IsTorsionStable
