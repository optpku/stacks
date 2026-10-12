/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.Presentation
public import ReasLib.Algebra.Module.RelativeDualizing.Flat
public import ReasLib.Algebra.Module.RelativeDualizing.BaseChange.Bijective
public import ReasLib.RingTheory.PicardGroup.Invertible
public import ReasLib.RingTheory.RingHom.Fiber.Module

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry Algebra.DualModule

universe u

namespace Algebra.RelativeDualizingModule.Presentation

/-- For a quasi-finite flat homomorphism of Noetherian rings, the relative dualizing
module of a finite/open presentation is invertible exactly when the relative dualizing
module of every residue-field fiber is invertible. -/
theorem invertible_iff_fiberwise
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B]
    (h_quasiFinite : RingHom.FiniteType.QuasiFinite (algebraMap A B))
    (P : Presentation (CommRingCat.ofHom (algebraMap A B))) :
    Module.Invertible B (P.module inferInstance inferInstance h_quasiFinite) ↔
      ∀ p : PrimeSpectrum A,
        Module.Invertible (p.asIdeal.Fiber B)
          (Algebra.DualModule.of p.asIdeal.ResidueField (p.asIdeal.Fiber B)) := sorry

end Algebra.RelativeDualizingModule.Presentation
