/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Noetherian
import StacksCheckRecall

/-!
# Lemma 33.11.1

The locally Noetherian field-extension equivalence is owned by
`ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Noetherian`.

@stack 038R
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

variable {k : Type u} [Field k]
variable {K : Type u} [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/- Lemma 33.11.1: local Noetherianity is invariant under finitely generated field extension. -/
@[stacks 038R] #check
  (AlgebraicGeometry.Scheme.Hom.isLocallyNoetherian_iff_isLocallyNoetherian_pullback_fieldExtension
      (k := k) (K := K) f :
    IsLocallyNoetherian X ↔
      IsLocallyNoetherian (FieldExtension.baseChange k K f))
