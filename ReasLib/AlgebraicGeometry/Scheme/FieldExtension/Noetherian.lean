/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.EssentialFiniteness
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally Noetherian schemes under field extension

This leaf owns the source-facing equivalence between local Noetherianity of a scheme over a field
and of its base change along a finitely generated field extension.

@stack 038R
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k]
variable {K : Type u} [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- A scheme over a field is locally Noetherian exactly when its base change along a finitely
generated field extension is locally Noetherian. -/
@[stacks 038R]
theorem isLocallyNoetherian_iff_isLocallyNoetherian_pullback_fieldExtension :
    IsLocallyNoetherian X ↔
      IsLocallyNoetherian (FieldExtension.baseChange k K f) := sorry

end AlgebraicGeometry.Scheme.Hom
