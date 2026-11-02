/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Diagonal

/-!
# Cancellation of morphism properties along postcomposition

Representability and the representable relative properties of being locally of
finite type, locally quasi-finite, separated, or a monomorphism pass from a
composite morphism of algebraic spaces to its first factor. An immersion
(resp. closed immersion) cancels against a locally separated (resp. separated)
postcomposition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

-- Factor through the graph, a base change of the second morphism's diagonal,
-- followed by a base change of the composite.
private theorem cancellation_of_diagonal {C : Type*} [Category* C] [HasPullbacks C]
    (P : MorphismProperty C) [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    {Z Y X : C} (f : Z ⟶ Y) (g : Y ⟶ X)
    (hgf : P (f ≫ g)) (hg : P (pullback.diagonal g)) : P f := by
  have hgraph : P (pullback.lift (𝟙 Z) f (by simp) : Z ⟶ pullback (f ≫ g) g) :=
    P.of_isPullback (pullback_lift_diagonal_isPullback f g) hg
  simpa only [pullback.lift_snd] using
    P.comp_mem _ (pullback.snd (f ≫ g) g) hgraph (P.pullback_snd _ _ hgf)

private theorem presheaf_cancellation_of_diagonal {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderComposition]
    {Z Y X : (Over S)ᵒᵖ ⥤ Type u} (f : Z ⟶ Y) (g : Y ⟶ X)
    (hgf : (over P).presheaf (f ≫ g))
    (hg : (over P).presheaf (pullback.diagonal g)) : (over P).presheaf f := by
  letI : (over P (X := S)).IsStableUnderComposition :=
    inferInstanceAs (P.inverseImage (Over.forget S)).IsStableUnderComposition
  letI := relative_isStableUnderBaseChange (over P) (F := yoneda (C := Over S))
  exact cancellation_of_diagonal _ f g hgf hg

/-- If a composite morphism of algebraic spaces is representable by schemes,
then so is the first factor. -/
theorem relativelyRepresentable_of_comp {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (f : Z ⟶ Y) (g : Y ⟶ X) (hgf : yoneda.relativelyRepresentable (f ≫ g)) :
    yoneda.relativelyRepresentable f := by
  exact cancellation_of_diagonal (C := (Over S)ᵒᵖ ⥤ Type u) _ f g hgf
    (relativelyRepresentable_diagonal g)

/-- If a composite morphism of algebraic spaces is representable and locally of
finite type, then so is the first factor. -/
theorem locallyOfFiniteType_of_comp {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (f : Z ⟶ Y) (g : Y ⟶ X)
    (hgf : (over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf (f ≫ g)) :
    (over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf f := by
  exact presheaf_cancellation_of_diagonal _ f g hgf
    ⟨relativelyRepresentable_diagonal g, (locallyOfFiniteType_diagonal g).property⟩

/-- If a composite morphism of algebraic spaces is representable, locally of
finite type, and locally quasi-finite, then so is the first factor. -/
theorem locallyQuasiFinite_of_comp {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (f : Z ⟶ Y) (g : Y ⟶ X)
    (hgf :
      (over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
        @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf
        (f ≫ g)) :
    (over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf f := by
  exact presheaf_cancellation_of_diagonal _ f g hgf
    ⟨relativelyRepresentable_diagonal g, (locallyQuasiFinite_diagonal g).property⟩

/-- If a composite morphism of algebraic spaces is representable and separated,
then so is the first factor. -/
theorem isSeparated_of_comp {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (f : Z ⟶ Y) (g : Y ⟶ X)
    (hgf : (over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf (f ≫ g)) :
    (over (@AlgebraicGeometry.IsSeparated : MorphismProperty Scheme.{u})).presheaf f := by
  exact presheaf_cancellation_of_diagonal _ f g hgf
    (isSeparated_diagonal g)

/-- If a composite morphism of algebraic spaces is representable and a
monomorphism, then so is the first factor. -/
theorem monomorphisms_of_comp {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (f : Z ⟶ Y) (g : Y ⟶ X)
    (hgf : (over (monomorphisms Scheme.{u})).presheaf (f ≫ g)) :
    (over (monomorphisms Scheme.{u})).presheaf f := by
  exact presheaf_cancellation_of_diagonal _ f g hgf
    (monomorphisms_diagonal g)

namespace IsImmersion

/-- If a composite morphism of algebraic spaces is an immersion and the second
factor is locally separated, then the first factor is an immersion. -/
theorem of_comp_of_locallySeparated {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (f : Z ⟶ Y) (g : Y ⟶ X) [IsImmersion (f ≫ g)] [LocallySeparated g] :
    IsImmersion f := by
  exact ⟨presheaf_cancellation_of_diagonal _ f g
    (IsImmersion.presheaf (f := f ≫ g))
    (LocallySeparated.isImmersion_diagonal (f := g))⟩

end IsImmersion

namespace IsClosedImmersion

/-- If a composite morphism of algebraic spaces is a closed immersion and the
second factor is separated, then the first factor is a closed immersion. -/
theorem of_comp_of_separated {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (f : Z ⟶ Y) (g : Y ⟶ X) [IsClosedImmersion (f ≫ g)] [Separated g] :
    IsClosedImmersion f := by
  exact ⟨presheaf_cancellation_of_diagonal _ f g
    (IsClosedImmersion.presheaf (f := f ≫ g))
    (FormalAlgebraicSpace.Separated.isClosedImmersion_diagonal (f := g))⟩

end IsClosedImmersion

/-- Immersions of algebraic spaces cancel against a locally separated
postcomposition. -/
instance isImmersion_hasOfPostcompProperty {S : Scheme.{u}} :
    HasOfPostcompProperty
      (@IsImmersion S : MorphismProperty (AlgebraicSpace S))
      (@LocallySeparated S) where
  of_postcomp f g hg hfg := by
    letI := hg
    letI := hfg
    exact IsImmersion.of_comp_of_locallySeparated f g

/-- Closed immersions of algebraic spaces cancel against a separated
postcomposition. -/
instance isClosedImmersion_hasOfPostcompProperty {S : Scheme.{u}} :
    HasOfPostcompProperty
      (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S))
      (@Separated S) where
  of_postcomp f g hg hfg := by
    letI := hg
    letI := hfg
    exact IsClosedImmersion.of_comp_of_separated f g

end AlgebraicGeometry.AlgebraicSpace
