/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
import StacksCheckRecall

/-!
# Characterizations of syntomicity for morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.36.4: Syntomicity of a morphism of algebraic spaces is equivalent
to the following nine pointwise, base-change, étale-local, and Zariski-local
conditions. -/
@[stacks 03ZA] #check (AlgebraicGeometry.AlgebraicSpace.syntomic_tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE
      [ Syntomic f
      , ∀ x : Points X, SyntomicAt f x
      , Syntomic.baseChangeOnSchemes f
      , Syntomic.baseChangeOnAffineSchemes f
      , Syntomic.existsSurjectiveEtaleTarget f
      , Syntomic.existsSurjectiveEtaleSource f
      , Syntomic.forallEtaleSquare f
      , Syntomic.existsEtaleSquare f
      , Syntomic.existsZariskiCover f ])

end AlgebraicGeometry.AlgebraicSpace
