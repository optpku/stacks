module

public import ReasLib.RingTheory.AdicCompletion.FiniteModule

@[expose] public section

universe u v

/- The adic completion of a finite module is finite over the completed ring. -/
#check (AdicCompletion.instModuleFinite :
    ∀ {A : Type u} [CommRing A] {I : Ideal A}
      {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M],
      Module.Finite (AdicCompletion I A) (AdicCompletion I M))
