module

public import ReasLib.Algebra.Module.RelativeDualizing.NoetherPairing.Bijective
public import ReasLib.Algebra.Module.RelativeDualizing.TraceElement
public import ReasLib.RingTheory.Kaehler.NoetherDifferent

@[expose] public section

open AlgebraicGeometry

universe u

namespace Algebra.RelativeDualizingModule

/-- The transpose of the Noether pairing evaluated at a universal trace element
agrees with multiplication on the annihilator of the diagonal ideal. -/
theorem noetherPairing_flip_apply_traceElement
    (A B' B : Type u) [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Flat A B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (tau : RelativeDualizingModule.of A B' B h_quasiFinite h_open)
    (h_tau : TraceElement.IsUniversal A B' B h_quasiFinite h_open tau)
    (xi : (KaehlerDifferential.ideal A B).annihilator) :
    (noetherPairing A B' B h_quasiFinite h_open).flip xi tau =
      Algebra.TensorProduct.lmul' A xi := sorry

/-- The Noether different is the range of evaluation at a universal trace element. -/
theorem noetherDifferent_eq_range_eval_traceElement
    (A B' B : Type u) [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Flat A B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (tau : RelativeDualizingModule.of A B' B h_quasiFinite h_open)
    (h_tau : TraceElement.IsUniversal A B' B h_quasiFinite h_open tau) :
    KaehlerDifferential.noetherDifferent A B =
      (Module.Dual.eval B
        (RelativeDualizingModule.of A B' B h_quasiFinite h_open) tau).range := sorry

end Algebra.RelativeDualizingModule
