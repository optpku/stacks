/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Basic

/-!
# Existence of Cartan--Eilenberg resolutions

This leaf records the reusable existence interface separately from any particular staircase
construction.  The lower-bound form is useful to inductive constructions, while the bundled
bounded-below form is the ordinary downstream entry point.
-/

@[expose] public section

open CategoryTheory ComplexShape

universe v u

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]

/-- A bounded-below cochain complex with a specified lower bound admits a Cartan--Eilenberg
resolution. -/
theorem nonempty_of_isStrictlyGE
    (K : CochainComplex.Plus A) {n : ℤ} (hK : K.obj.IsStrictlyGE n) :
    Nonempty (CartanEilenbergResolution K) := sorry

/-- Lemma 13.21.2 (tag 015I): every bounded-below cochain complex in an abelian category with
enough injectives admits a Cartan--Eilenberg resolution. -/
@[stacks 015I]
theorem nonempty (K : CochainComplex.Plus A) :
    Nonempty (CartanEilenbergResolution K) := sorry

end CochainComplex.CartanEilenbergResolution
