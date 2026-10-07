module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_4_2_Separation

/-!
# Cancellation of immersions along postcomposition

If a composite morphism of algebraic spaces is representable, locally of finite
type, locally quasi-finite, separated, and a monomorphism in the sense of
Definition 65.5.1, then so is the first factor. An immersion (resp. closed
immersion) cancels against a locally separated (resp. separated) postcomposition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If a composite morphism of algebraic spaces is representable in the sense of
Definition 65.5.1, then so is the first factor. -/
theorem relativelyRepresentable_of_comp {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (f : Z ⟶ Y) (g : Y ⟶ X) (hgf : yoneda.relativelyRepresentable (f ≫ g)) :
    yoneda.relativelyRepresentable f :=
  sorry

/-- If a composite morphism of algebraic spaces is locally of finite type in the
sense of Definition 65.5.1, then so is the first factor. -/
theorem locallyOfFiniteType_of_comp {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (f : Z ⟶ Y) (g : Y ⟶ X)
    (hgf : (over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf (f ≫ g)) :
    (over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf f :=
  sorry

/-- If a composite morphism of algebraic spaces is locally quasi-finite in the
sense of Definition 65.5.1, then so is the first factor. -/
theorem locallyQuasiFinite_of_comp {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (f : Z ⟶ Y) (g : Y ⟶ X)
    (hgf :
      (over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
        @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf
        (f ≫ g)) :
    (over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf f :=
  sorry

/-- If a composite morphism of algebraic spaces is separated in the sense of
Definition 65.5.1, then so is the first factor. -/
theorem isSeparated_of_comp {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (f : Z ⟶ Y) (g : Y ⟶ X)
    (hgf : (over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf (f ≫ g)) :
    (over (@AlgebraicGeometry.IsSeparated : MorphismProperty Scheme.{u})).presheaf f :=
  sorry

/-- If a composite morphism of algebraic spaces is a monomorphism in the sense of
Definition 65.5.1, then so is the first factor. -/
theorem monomorphisms_of_comp {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (f : Z ⟶ Y) (g : Y ⟶ X)
    (hgf : (over (monomorphisms Scheme.{u})).presheaf (f ≫ g)) :
    (over (monomorphisms Scheme.{u})).presheaf f :=
  sorry

namespace IsImmersion

/-- If a composite morphism of algebraic spaces is an immersion and the second
factor is locally separated, then the first factor is an immersion. -/
theorem of_comp_of_locallySeparated {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (f : Z ⟶ Y) (g : Y ⟶ X) [IsImmersion (f ≫ g)] [LocallySeparated g] :
    IsImmersion f :=
  sorry

end IsImmersion

namespace IsClosedImmersion

/-- If a composite morphism of algebraic spaces is a closed immersion and the
second factor is separated, then the first factor is a closed immersion. -/
theorem of_comp_of_separated {S : Scheme.{u}} {Z Y X : AlgebraicSpace S}
    (f : Z ⟶ Y) (g : Y ⟶ X) [IsClosedImmersion (f ≫ g)] [Separated g] :
    IsClosedImmersion f :=
  sorry

end IsClosedImmersion

/-- Immersions of algebraic spaces cancel against a locally separated
postcomposition. -/
instance isImmersion_hasOfPostcompProperty {S : Scheme.{u}} :
    HasOfPostcompProperty
      (@IsImmersion S : MorphismProperty (AlgebraicSpace S))
      (@LocallySeparated S) :=
  sorry

/-- Closed immersions of algebraic spaces cancel against a separated
postcomposition. -/
instance isClosedImmersion_hasOfPostcompProperty {S : Scheme.{u}} :
    HasOfPostcompProperty
      (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S))
      (@Separated S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
