/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Stein.Etale
import StacksCheckRecall

/-!
# Finite étaleness of the Stein second factor

A proper morphism of algebraic spaces that is of finite presentation, flat, and
has geometrically reduced fibres has finite étale Stein second factor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.36.9 (1): let `S` be a scheme and let `f : X ⟶ Y` be a proper
morphism of algebraic spaces over `S`. If `f` is of finite presentation, flat,
and has geometrically reduced fibres in the sense of Definition 76.29.2, then
the Stein factorization map `Hom.fromNormalization f : Hom.normalization f ⟶ Y`
of Theorem 76.36.5, with first factor `Hom.toNormalization f`, is finite. -/
@[stacks 0E0D] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.instIsFiniteFromNormalizationOfFlatGeometricallyReduced :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Proper f] [FinitePresentation f] [Flat f]
      [Hom.HasReducedGeometricFibres f],
      IsFinite (Hom.fromNormalization f))

/- Lemma 76.36.9 (2): under the same hypotheses, the Stein factorization map
`Hom.fromNormalization f : Hom.normalization f ⟶ Y` of Theorem 76.36.5, with
first factor `Hom.toNormalization f`, is étale. -/
@[stacks 0E0D] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.instEtaleFromNormalizationOfFlatGeometricallyReduced :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Proper f] [FinitePresentation f] [Flat f]
      [Hom.HasReducedGeometricFibres f],
      Etale (Hom.fromNormalization f))

end AlgebraicGeometry.AlgebraicSpace
