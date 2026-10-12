/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.SetTheory.ZFC.VonNeumann

@[expose] public section

universe u

namespace ZFSet

/-- Every set belongs to a level of the von Neumann hierarchy. -/
theorem exists_mem_vonNeumannLevel (x : ZFSet.{u}) :
    ∃ ordinal : Ordinal.{u}, x ∈ vonNeumann ordinal :=
  ZFSet.exists_mem_vonNeumann x

end ZFSet
