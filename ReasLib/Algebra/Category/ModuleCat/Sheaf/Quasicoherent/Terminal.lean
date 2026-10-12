/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section

open CategoryTheory Limits

universe u v w

namespace SheafOfModules.IsQuasicoherent

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A sheaf of modules on a ringed site with terminal object `S` is quasicoherent
if and only if there is a covering family of `S` on whose slice restrictions
the sheaf admits presentations. -/
theorem iff_existsPresentation_of_isTerminal
    (M : SheafOfModules.{w} R) (S : C) (hS : IsTerminal S) :
    M.IsQuasicoherent ↔
      ∃ (I : Type u) (X : I → C),
        Sieve.ofObjects X S ∈ J S ∧
          ∀ i : I, Nonempty (M.over (X i)).Presentation := sorry

end SheafOfModules.IsQuasicoherent
