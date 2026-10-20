/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Chow.FiniteComponents

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 32.12.3: let `S` be quasi-compact and quasi-separated, and let `f : X ⟶ S` be a
separated morphism of finite type. If `X` has finitely many irreducible components, then there is
a Chow modification of `f` whose proper surjective morphism is an isomorphism over a dense open
of `X`. -/
@[stacks 0203] #check
  (AlgebraicGeometry.ChowLemmaModification.exists_of_separated_finiteType_of_finite_irreducibleComponents :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
      [IsSeparated f] [Scheme.Hom.FiniteType f] [Finite (irreducibleComponents X)],
      Nonempty (AlgebraicGeometry.ChowLemmaModification f))
