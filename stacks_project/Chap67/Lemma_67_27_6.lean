/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Locality
import StacksCheckRecall

/-!
# Characterizations of local quasi-finiteness for morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

/- Lemma 67.27.6: The nine local characterizations of locally quasi-finite
morphisms of algebraic spaces, including the local-finite-type requirement. -/
@[stacks 040Z] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_tfae.{u, v} :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      List.TFAE
        [ LocallyOfFiniteType f ∧ LocallyQuasiFinite f
        , ∀ x : Points X, ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
            IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
              LocallyOfFiniteType (i ≫ f) ∧ LocallyQuasiFinite (i ≫ f)
        , LocallyQuasiFinite.baseChangeOnSchemes f
        , LocallyQuasiFinite.baseChangeOnAffineSchemes f
        , LocallyQuasiFinite.existsSurjectiveEtaleTarget f
        , LocallyQuasiFinite.existsSurjectiveEtaleSource f
        , LocallyQuasiFinite.forallEtaleSquare f
        , LocallyQuasiFinite.existsEtaleSquare f
        , LocallyQuasiFinite.existsZariskiCover.{u, v} f ])
