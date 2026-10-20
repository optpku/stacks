/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.DenseOpen
import StacksCheckRecall

/-!
# Extending open immersions from a dense open of algebraic spaces

A morphism of algebraic spaces that is separated, locally of finite type, and
flat is an open immersion if it is an isomorphism over a quasi-compact
scheme-theoretically dense open of the target.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 76.37.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `ι : V ⟶ Y` be an open immersion (an open
subspace of `Y`). Assume `f` is separated, locally of finite type, and flat,
`ι` is quasi-compact and scheme-theoretically dense, and the restriction
`openInverseImageTo f ι : openInverseImage f ι ⟶ V` is an isomorphism. Then
`f` is an open immersion. -/
@[stacks 0879] #check
  (AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion.of_isIso_restrict_of_flat :
    ∀ {S : Scheme.{u}} {X Y V : AlgebraicSpace S} (f : X ⟶ Y),
      [AlgebraicSpace.Separated f] →
      [AlgebraicSpace.LocallyOfFiniteType f] →
      [AlgebraicSpace.Flat f] →
      (ι : V ⟶ Y) →
      [AlgebraicSpace.IsOpenImmersion ι] →
      [AlgebraicSpace.QuasiCompact ι] →
      [AlgebraicSpace.IsSchemeTheoreticallyDense ι] →
      [IsIso (AlgebraicSpace.openInverseImageTo f ι)] →
      AlgebraicSpace.IsOpenImmersion f)
