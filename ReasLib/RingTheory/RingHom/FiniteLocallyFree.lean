/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.LocallyFree

@[expose] public section

universe u v

namespace RingHom

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- A ring morphism `f : A →+* B` is finite locally free of rank `r` if `B` is finite
locally free of rank `r` as an `A`-module along `f`. -/
def FiniteLocallyFreeOfRank (f : A →+* B) (r : ℕ) : Prop :=
  -- Local instance justification (noncanonical choice): the algebra is induced by the given ring hom.
  let _ : Algebra A B := f.toAlgebra
  Module.FiniteLocallyFreeOfRank A B r

/-- Finite local freeness of rank `r` for `algebraMap A B` is equivalent to
`Module.FiniteLocallyFreeOfRank A B r`. -/
theorem finiteLocallyFreeOfRank_algebraMap [Algebra A B] {r : ℕ} :
    (algebraMap A B).FiniteLocallyFreeOfRank r ↔ Module.FiniteLocallyFreeOfRank A B r := sorry

end RingHom
