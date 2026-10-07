module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Module.RelativeDualizing.BaseChange

@[expose] public section

open AlgebraicGeometry
open scoped Algebra.RelativeDual

universe u

namespace Algebra.RelativeDualizingModule

/-- Under a flat quasi-finite algebra map of Noetherian rings, the chosen
relative dualizing module is flat over the base ring. -/
instance flat
    (A B' B : Type u)
    [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Module.Flat A B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))) :
    Module.Flat A (of A B' B h_quasiFinite h_open) := sorry

end Algebra.RelativeDualizingModule
