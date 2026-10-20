/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation.Locality
import StacksCheckRecall

/-!
# Characterizations of local finite presentation for morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.28.4 -/
@[stacks 0410] #check (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_tfae.{u, v} :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE
      [ LocallyOfFinitePresentation f
      , ∀ x : Points X, FinitePresentationAt f x
      , LocallyOfFinitePresentation.baseChangeOnSchemes f
      , LocallyOfFinitePresentation.baseChangeOnAffineSchemes f
      , LocallyOfFinitePresentation.existsSurjectiveEtaleTarget f
      , LocallyOfFinitePresentation.existsSurjectiveEtaleSource f
      , LocallyOfFinitePresentation.forallEtaleSquare f
      , LocallyOfFinitePresentation.existsEtaleSquare f
      , LocallyOfFinitePresentation.existsZariskiCover.{u, v} f ])

end AlgebraicGeometry.AlgebraicSpace
