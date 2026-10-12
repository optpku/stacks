/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The spectrum of a field is a Noetherian scheme. -/
instance instIsNoetherian_specOfField {k : Type u} [Field k] :
    IsNoetherian (Spec (CommRingCat.of k)) := sorry

/-- A morphism of schemes to the spectrum of a field is flat. -/
instance instFlat_hom {k : Type u} [Field k] (X : SchemeOverField k) :
    Flat X.hom := sorry

end AlgebraicGeometry.SchemeOverField

end
