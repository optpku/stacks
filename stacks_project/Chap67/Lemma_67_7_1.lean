/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Submersive
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry MorphismProperty
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.7.1: A representable morphism of algebraic spaces over a scheme is
universally submersive on represented scheme base changes if and only if every
algebraic-space base change induces a quotient map on underlying point spaces. -/
@[stacks 0CFQ] #check
  (AlgebraicGeometry.AlgebraicSpace.universallySubmersive_presheaf_iff_universally_pointsIsQuotientMap :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
      (hf : yoneda.relativelyRepresentable f),
      (over (@AlgebraicGeometry.UniversallySubmersive :
        MorphismProperty Scheme.{u})).presheaf f ↔
        universally pointsIsQuotientMap f)
