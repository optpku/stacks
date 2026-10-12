/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.BaseChange
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Weakly associated points under field extension

Weak association of a point to a quasicoherent module descends along the
projection from a field-extension base change.
-/

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.FieldExtension

variable {k : Type u} [Field k]
variable {K : Type u} [Field K] [Algebra k K]
variable {X : Scheme.{u}}

/-- A weakly associated point of the base change of a quasicoherent module maps to a weakly
associated point of the original module. -/
@[stacks 0CUC]
theorem mem_weakAss_of_mem_weakAss
    (f : X ⟶ Spec (CommRingCat.of k)) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (y : AlgebraicGeometry.FieldExtension.baseChange k K f)
    (hy : y ∈ (Scheme.Modules.FieldExtension.baseChange k K f ℱ).weakAss) :
    AlgebraicGeometry.FieldExtension.toSource k K f y ∈ ℱ.weakAss := sorry

end AlgebraicGeometry.Scheme.Modules.FieldExtension
