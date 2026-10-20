/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.ResidueField.FlatExtension
import StacksCheckRecall

universe u v

@[expose] public section

/- Remark 111.5.8: the flat local residue-field-lifting existence of
Exercise 111.5.7 holds for an arbitrary field extension `K/k`. If
`(A, m, k)` is a local ring and `K/k` is any field extension, there
exists a flat local map of local rings `A → B` such that
`m_B = m B` and `B / m B ≃ K` as a `k`-algebra. This is
`IsLocalRing.ResidueField.exists_flat_localExtension`. -/
@[stacks 02CX]
#check (IsLocalRing.ResidueField.exists_flat_localExtension :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (K : Type v) [Field K]
    [Algebra (IsLocalRing.ResidueField R) K],
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : IsLocalRing R')
      (_ : Algebra R R') (_ : IsLocalHom (algebraMap R R'))
      (_ : (algebraMap R R').Flat)
      (_ : IsLocalRing.ResidueField R' ≃ₐ[IsLocalRing.ResidueField R] K),
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) =
        IsLocalRing.maximalIdeal R')
