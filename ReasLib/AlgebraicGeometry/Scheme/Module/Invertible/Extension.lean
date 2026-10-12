/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

/-!
# Extension of invertible module sheaves

This file owns extension results for invertible module sheaves from open subschemes.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- An invertible module on an open subscheme extends over a locally Noetherian ambient scheme
when every stalk outside the open is a unique factorization monoid. -/
@[stacks 0BD9]
theorem exists_extension_of_stalks_uniqueFactorizationMonoid
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    (ℒ : U.toScheme.Modules) [Scheme.Modules.Invertible ℒ]
    (hUFD : ∀ x : X, x ∉ (U : Set X) → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ (ℒ' : X.Modules) (_ : Scheme.Modules.Invertible ℒ'),
      Nonempty (ℒ ≅ (Scheme.Modules.pullback U.ι).obj ℒ') := sorry

end AlgebraicGeometry.Scheme.Modules.Invertible
