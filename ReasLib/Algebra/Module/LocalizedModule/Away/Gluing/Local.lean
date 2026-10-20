/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Local Recovery for Principal-Open Module Gluing

@stack 00EQ

This leaf records finite local recovery for a module assembled from
compatible principal-open sections.  The recovery map needs a finite indexing
type because localization commutes with the finite product of local pieces.
The pairwise-overlap formula belongs to `Gluing.Basic`, where it has no
finiteness hypothesis.
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u v w

namespace LocalizedModule.Away.Gluing

variable {R : Type u} [CommRing R]
variable {ι : Type w} {f : ι → R}

/-- The linear equivalence induced by a localized projection when its
bijectivity has been supplied explicitly.  This constructor is independent
of any particular local-recovery proof. -/
@[stacks 00EQ "principal-open gluing local recovery equivalence"]
noncomputable def localizedProjectionEquiv (glue : Gluing f) (i : ι)
    (h : Function.Bijective (glue.localizedProjection i)) :
    LocalizedModule.Away (f i) glue.gluedModule ≃ₗ[Localization.Away (f i)]
      glue.localModule i :=
  LinearEquiv.ofBijective (glue.localizedProjection i) h

/-- The forward linear map of `localizedProjectionEquiv` is the localized
projection from which it is constructed. -/
@[simp, stacks 00EQ "principal-open gluing local recovery equivalence map"]
theorem localizedProjectionEquiv_toLinearMap (glue : Gluing f) (i : ι)
    (h : Function.Bijective (glue.localizedProjection i)) :
    (localizedProjectionEquiv glue i h).toLinearMap = glue.localizedProjection i := sorry

/-- Applying `localizedProjectionEquiv` agrees with the localized
projection map. -/
@[simp, stacks 00EQ "principal-open gluing local recovery equivalence application"]
theorem localizedProjectionEquiv_apply (glue : Gluing f) (i : ι)
    (h : Function.Bijective (glue.localizedProjection i))
    (x : LocalizedModule.Away (f i) glue.gluedModule) :
    localizedProjectionEquiv glue i h x = glue.localizedProjection i x := sorry

/-- Tag `00EQ` (1): for a finite family of principal-open modules with
compatible overlap identifications, localizing the compatible-family module
away from `f i` recovers its `i`-th local piece. -/
@[stacks 00EQ "principal-open gluing local recovery"]
theorem localizedProjection_bijective [Finite ι] (glue : Gluing f) (i : ι) :
    Function.Bijective (glue.localizedProjection i) := sorry

end LocalizedModule.Away.Gluing
