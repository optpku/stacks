/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyUnramified.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.InfinitesimalNeighbourhood.UniversalFirstOrder
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.InfinitesimalNeighbourhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.7.3 (1): an immersion of schemes is formally unramified. -/
@[stacks 04F5] #check
  (AlgebraicGeometry.IsImmersion.formallyUnramified :
    ∀ {Z X : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
      [AlgebraicGeometry.IsImmersion i], AlgebraicGeometry.FormallyUnramified i)

/- Lemma 37.7.3 (2): the first infinitesimal neighbourhood of an immersion is its
universal first-order thickening over the ambient scheme. -/
@[stacks 04F5] #check
  (AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood.firstOrderOver_isUniversal :
    ∀ {Z X : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
      [AlgebraicGeometry.IsImmersion i],
      AlgebraicGeometry.Thickening.IsUniversalFirstOrder
        (AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood.firstOrderOver i))

/- Lemma 37.7.3 (3): the ambient conormal sheaf of an immersion agrees, via the canonical
comparison isomorphism, with its conormal sheaf in the first infinitesimal neighbourhood. -/
@[stacks 04F5] #check
  (AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood.conormalComparison_isIso :
    ∀ {Z X : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
      [AlgebraicGeometry.IsImmersion i],
      CategoryTheory.IsIso
        (AlgebraicGeometry.Scheme.Hom.Conormal.factorizationConormalComparison i
          (AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood.fromSource i 1)
          (AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood.toAmbient i 1)
          (AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood.fromSource_toAmbient i 1)))
