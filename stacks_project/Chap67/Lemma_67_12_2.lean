/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.12.2 (1): let `S` be a scheme and let `Z ⟶ Y ⟶ X` be morphisms of
algebraic spaces over `S`. If `Z ⟶ X` is representable, locally of finite type,
locally quasi-finite, separated, and a monomorphism, then so is `Z ⟶ Y`. -/
@[stacks 0AGC] #check
  (AlgebraicGeometry.AlgebraicSpace.relativelyRepresentable_of_comp :
    ∀ {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (f : Z ⟶ Y) (g : Y ⟶ X),
      yoneda.relativelyRepresentable (f ≫ g) → yoneda.relativelyRepresentable f)

@[stacks 0AGC] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyOfFiniteType_of_comp :
    ∀ {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (f : Z ⟶ Y) (g : Y ⟶ X),
      (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
          MorphismProperty Scheme.{u})).presheaf (f ≫ g) →
        (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
            MorphismProperty Scheme.{u})).presheaf f)

@[stacks 0AGC] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_of_comp :
    ∀ {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (f : Z ⟶ Y) (g : Y ⟶ X),
      (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
        @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf
          (f ≫ g) →
        (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
          @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf f)

@[stacks 0AGC] #check
  (AlgebraicGeometry.AlgebraicSpace.isSeparated_of_comp :
    ∀ {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (f : Z ⟶ Y) (g : Y ⟶ X),
      (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
          MorphismProperty Scheme.{u})).presheaf (f ≫ g) →
        (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
            MorphismProperty Scheme.{u})).presheaf f)

@[stacks 0AGC] #check
  (AlgebraicGeometry.AlgebraicSpace.monomorphisms_of_comp :
    ∀ {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (f : Z ⟶ Y) (g : Y ⟶ X),
      (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf
          (f ≫ g) →
        (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf f)

/- Lemma 67.12.2 (2): if `Z ⟶ X` is an immersion and `Y ⟶ X` is locally
separated, then `Z ⟶ Y` is an immersion. -/
@[stacks 0AGC] #check
  (AlgebraicGeometry.AlgebraicSpace.IsImmersion.of_comp_of_locallySeparated :
    ∀ {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (f : Z ⟶ Y) (g : Y ⟶ X)
      [AlgebraicSpace.IsImmersion (f ≫ g)] [LocallySeparated g],
      AlgebraicSpace.IsImmersion f)

/- Lemma 67.12.2 (3): if `Z ⟶ X` is a closed immersion and `Y ⟶ X` is
separated, then `Z ⟶ Y` is a closed immersion. -/
@[stacks 0AGC] #check
  (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.of_comp_of_separated :
    ∀ {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (f : Z ⟶ Y) (g : Y ⟶ X)
      [AlgebraicSpace.IsClosedImmersion (f ≫ g)] [Separated g],
      AlgebraicSpace.IsClosedImmersion f)
