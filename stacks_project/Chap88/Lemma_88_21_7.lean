/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective.Etale
import StacksCheckRecall

/-!
# Étale covering morphisms are rig-surjective

A morphism of locally Noetherian formal algebraic spaces that is representable
by algebraic spaces, étale, and surjective is rig-surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace

universe u

/- Lemma 88.21.7: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
locally Noetherian formal algebraic spaces which is representable by algebraic
spaces, étale, and surjective. Then `f` is rig-surjective. -/
@[stacks 0AQU] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective.of_etale :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [hf : Etale f]
    (h_surj : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Surjective
        (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom hf.representable ξ)),
    RigSurjective f)
