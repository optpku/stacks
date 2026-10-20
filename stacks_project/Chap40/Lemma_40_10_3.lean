/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.FiberComparison.Field
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

/- Lemma 40.10.3: after a common field extension, two arrows of a groupoid scheme
over a field spectrum lift to points related by an automorphism over the extended field. -/
@[stacks 04LP] #check
  (AlgebraicGeometry.GroupoidScheme.existsSourceBaseChangeIso_mapPoints :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      {k : Type u} [Field k]
      (eU : AlgebraicGeometry.Spec (CommRingCat.of k) ≅ G.U.left) (r r' : G.R.left),
    ∃ (K : Type u) (_ : Field K) (ι : k →+* K),
      let f := AlgebraicGeometry.Spec.map (CommRingCat.ofHom ι) ≫ eU.hom
      let R' : Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
        Over.mk (pullback.snd G.s.left f)
      ∃ (φ : R' ≅ R') (r₁ r₂ : R'.left),
        φ.hom.left r₁ = r₂ ∧
          pullback.fst G.s.left f r₁ = r ∧
          pullback.fst G.s.left f r₂ = r')
