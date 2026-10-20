/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.CompactOpen

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 33.7.9 (1): a quasi-compact open after a possibly infinite Galois field extension
descends to a finite intermediate field. -/
@[stacks 04KU "(1)"]
#check
  (AlgebraicGeometry.FieldExtension.Galois.CompactOpen.exists_finiteSubextension_preimage_eq :
    ∀ {k kbar : Type u} [Field k] [Field kbar] [Algebra k kbar] [IsGalois k kbar]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
      (V : CompactOpens (FieldExtension.baseChange k kbar f).carrier),
      ∃ K' : IntermediateField k kbar, FiniteDimensional k K' ∧
        ∃ V' : CompactOpens (FieldExtension.baseChange k K' f).carrier,
          (Opens.map
            (Scheme.AffineBaseChange.Subalgebra.map f K'.toSubalgebra).base).obj V'.toOpens =
              V.toOpens)

/- Lemma 33.7.9 (2): a quasi-compact open after a possibly infinite Galois field extension is
stabilized by an open subgroup of the Galois group. -/
@[stacks 04KU "(2)"]
#check
  (AlgebraicGeometry.FieldExtension.Galois.CompactOpen.exists_openSubgroup_stabilizing :
    ∀ {k kbar : Type u} [Field k] [Field kbar] [Algebra k kbar] [IsGalois k kbar]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
      (V : CompactOpens (FieldExtension.baseChange k kbar f).carrier),
      ∃ H : OpenSubgroup Gal(kbar/k),
        ∀ σ : H,
          (Opens.map (FieldExtension.Galois.map k kbar f σ.1).base).obj V.toOpens = V.toOpens)
