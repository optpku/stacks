/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.TraceElement
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open Algebra.RelativeDualizingModule
open Algebra.RelativeDualizingModule.TraceElement

universe u

/- Lemma 49.4.6: a flat quasi-finite map of Noetherian rings admits a trace
element in its relative dualizing module. -/
@[stacks 0BTB]
#check (Algebra.RelativeDualizingModule.TraceElement.exists_of_flat_quasiFinite :
    ∀ (A B' B : Type u)
      [CommRing A] [CommRing B'] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
      [Module.Flat A B]
      (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
      [Module.Finite A B']
      (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B)))),
      ∃ τ : of A B' B h_quasiFinite h_open,
        IsUniversal A B' B h_quasiFinite h_open τ)
