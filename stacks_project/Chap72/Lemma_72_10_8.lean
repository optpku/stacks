/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OverField.QuasiFinite

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 72.10.8: For an algebraic space over a field, local quasi-finiteness
is equivalent to local finite type and dimension zero, to being a scheme with
either property, and to being a disjoint union of spectra of finite-dimensional
local Artinian algebras over the field. Dimension at most zero includes the
empty space. -/
@[stacks 06S0] #check
  (AlgebraicGeometry.AlgebraicSpace.tfae_locallyQuasiFinite_over_field :
    ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (CommRingCat.of k))),
      List.TFAE
        [ LocallyOfFiniteType (SchemeRealization.toBase X) ∧
            LocallyQuasiFinite (SchemeRealization.toBase X)
        , LocallyOfFiniteType (SchemeRealization.toBase X) ∧ dimension X ≤ 0
        , IsScheme X ∧ LocallyOfFiniteType (SchemeRealization.toBase X) ∧
            LocallyQuasiFinite (SchemeRealization.toBase X)
        , IsScheme X ∧ LocallyOfFiniteType (SchemeRealization.toBase X) ∧ dimension X ≤ 0
        , Nonempty (FiniteLocalArtinianCoproduct X) ])

