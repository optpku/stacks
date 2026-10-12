/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Noetherian
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 30.10.1: for a Noetherian scheme `X` and a coherent module `ℱ` on `X`, every
monotone ℕ-indexed chain of quasicoherent subobjects of `ℱ` is eventually constant. -/
@[stacks 01Y8] #check (
  AlgebraicGeometry.Scheme.Modules.quasiCoherentSubobject_monotone_stabilizes :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      (ℱ : X.Modules) [ℱ.IsCoherent]
      (f : ℕ →o Subobject ℱ)
      (_ : ∀ n : ℕ, (((f n : Subobject ℱ) : X.Modules)).IsQuasicoherent),
      ∃ n : ℕ, ∀ m : ℕ, n ≤ m → f n = f m)
