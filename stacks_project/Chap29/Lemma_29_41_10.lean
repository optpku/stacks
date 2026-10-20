/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.41.10 (1): in a commutative triangle `X ⟶ Y ⟶ S`, if `X` is
universally closed over `S` and `Y` is separated and locally of finite type over
`S`, then the scheme-theoretic image of `h : X ⟶ Y` is proper over `S`. -/
@[stacks 0AH6] #check
  (AlgebraicGeometry.Scheme.Hom.imageι_comp_isProper_of_universallyClosed :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (h : X ⟶ Y) (f : X ⟶ S)
      (g : Y ⟶ S) (_hcomm : h ≫ g = f) [AlgebraicGeometry.UniversallyClosed f]
      [AlgebraicGeometry.IsSeparated g] [AlgebraicGeometry.LocallyOfFiniteType g],
      AlgebraicGeometry.IsProper (h.imageι ≫ g))

/- Lemma 29.41.10 (2): under the same hypotheses, the canonical morphism from `X`
to the scheme-theoretic image of `h : X ⟶ Y` is surjective. -/
@[stacks 0AH6] #check
  (AlgebraicGeometry.Scheme.Hom.toImage_surjective_of_universallyClosed :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (h : X ⟶ Y) (f : X ⟶ S)
      (g : Y ⟶ S) (_hcomm : h ≫ g = f) [AlgebraicGeometry.UniversallyClosed f]
      [AlgebraicGeometry.IsSeparated g] [AlgebraicGeometry.LocallyOfFiniteType g],
      AlgebraicGeometry.Surjective h.toImage)
