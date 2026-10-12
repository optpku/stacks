/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Forget
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat differential graded modules

K-flatness of a differential graded module is a property of its underlying complex over the
ground ring.  This file owns that bridge independently of property P or base change.
@stack 06XZ
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R}

/-- A right differential graded module is K-flat over the ground ring when its underlying
cochain complex is K-flat over that ring. -/
@[stacks 06XZ "differential graded module over the ground ring"]
def IsKFlat (M : DifferentialGradedModule.{u, v} A) : Prop :=
  M.toCochainComplex.IsKFlatOver

/-- K-flatness of a differential graded module is K-flatness over the ground ring of its
underlying cochain complex. -/
theorem isKFlat_iff (M : DifferentialGradedModule.{u, v} A) :
    M.IsKFlat ↔ M.toCochainComplex.IsKFlatOver := sorry

/-- The object property of K-flat right differential graded modules. -/
@[stacks 06XZ "K-flat differential graded modules"]
def kFlat : ObjectProperty (DifferentialGradedModule.{u, v} A) :=
  fun M ↦ M.IsKFlat

/-- Membership in `kFlat` is the K-flatness predicate. -/
theorem mem_kFlat (M : DifferentialGradedModule.{u, v} A) :
    kFlat M ↔ M.IsKFlat := sorry

end DifferentialGradedModule
