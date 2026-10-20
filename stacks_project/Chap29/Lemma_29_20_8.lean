/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Fiber
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 29.20.8: for a locally finite type morphism of schemes, local quasi-finiteness is
equivalent to discreteness of every scheme-theoretic fiber and to discreteness after every base
change from the spectrum of a field. -/
@[stacks 06RT] #check
  (AlgebraicGeometry.Scheme.Hom.locallyQuasiFinite_tfae_discrete_fibers :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f],
      List.TFAE
        [ LocallyQuasiFinite f
        , ∀ s : S, DiscreteTopology (f.fiber s)
        , ∀ (k : Type u) [Field k] (g : Spec (CommRingCat.of k) ⟶ S),
            DiscreteTopology (pullback f g : Scheme)
        ])
