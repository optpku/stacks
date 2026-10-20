/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Differentials
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.InfinitesimalNeighbourhood.UniversalProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.InfinitesimalNeighbourhood
import StacksCheckRecall

/-!
# Immersions of algebraic spaces and universal first-order thickenings

An immersion of algebraic spaces is formally unramified. Its universal
first-order thickening over the ambient space is the first-order infinitesimal
neighbourhood, and the two conormal sheaves agree.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.15.6: Let `S` be a scheme and `i : Z ⟶ X` an immersion of
algebraic spaces over `S`. Then (1) `i` is formally unramified, (2) its universal
first-order thickening over `X` is the first-order infinitesimal neighbourhood
of Definition 76.12.1, and (3) its conormal sheaves in the senses of
Definitions 76.5.1 and 76.15.5 agree. The main check records the unique-extension
property of the canonical first-order infinitesimal neighbourhood. -/
@[stacks 0608]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood.existsUnique_lift_firstOrder :
  ∀ {S : Scheme.{u}} {Z X T T' : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] (j : T ⟶ T') [IsFirstOrderThickening j]
    (a : T ⟶ Z) (b : T' ⟶ X) (sq : CommSq a j i b),
    Nonempty (Unique
      (Hom.InfinitesimalNeighbourhood.factorizationCommSq i 1 j a b sq).LiftStruct))

/- Composing these two implications proves assertion (1): every immersion is
unramified, and every unramified morphism is formally unramified. -/
#check (AlgebraicGeometry.AlgebraicSpace.unramified_of_isImmersion :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i],
    Unramified i)

#check (AlgebraicGeometry.AlgebraicSpace.formallyUnramified_of_unramified :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [Unramified i],
    FormallyUnramified i)

/- Together with the unique-extension property, first-order thickness gives
assertion (2). -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood.fromSource_isFirstOrderThickening :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i],
    IsFirstOrderThickening (Hom.InfinitesimalNeighbourhood.fromSource i 1))

/- The canonical comparison identifies the two conormal sheaves in assertion (3). -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood.conormalComparison_isIso :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i],
    IsIso (Hom.InfinitesimalNeighbourhood.conormalComparison i))
