/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.Algebra.Module.Reflexive.Counterexample
public import ReasLib.AlgebraicGeometry.Scheme.Module.RankOneReflexive.Tensor

/-!
# A rank-one reflexive sheaf with noninvertible duality behavior

The affine algebraic reflexive-module counterexample gives a coherent rank-one reflexive sheaf
whose internal Hom is not recovered by reflexive dual tensor, and whose tensor with its dual is
not the structure sheaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.ReflexiveCounterexample

variable (k : Type u) [Field k]

/-- The affine scheme associated to the counterexample subalgebra. -/
abbrev scheme : Scheme.{u} :=
  Spec (CommRingCat.of (Module.ReflexiveCounterexample.ring k))

/-- The quasi-coherent sheaf associated to the ambient polynomial module. -/
noncomputable def sheaf : (scheme k).Modules :=
  tilde (Module.ReflexiveCounterexample.ambientModule k)

/-- The counterexample sheaf is coherent reflexive and has rank one at the generic point. -/
theorem rankOneReflexive_sheaf :
    rankOneReflexiveModuleProperty (scheme k) (sheaf k) := sorry

/-- Internal Hom of the counterexample sheaf with itself is not isomorphic to the reflexive hull
of its dual tensored with itself. -/
theorem internalHom_not_iso_reflexiveHull_dual_tensor :
    ¬ Nonempty
      (internalHom (sheaf k) (sheaf k) ≅
        reflexiveHull (dual (sheaf k) ⊗ sheaf k)) := sorry

/-- The reflexive hull of the counterexample sheaf tensored with its dual is not isomorphic to
the structure sheaf. -/
theorem reflexiveHull_tensor_dual_not_iso_unit :
    ¬ Nonempty
      (reflexiveHull (sheaf k ⊗ dual (sheaf k)) ≅ 𝟙_ (scheme k).Modules) := sorry

end AlgebraicGeometry.Scheme.Modules.ReflexiveCounterexample
