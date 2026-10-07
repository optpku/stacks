module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap67.Definition_67_4_2_Separation

/-!
# Properties of the relative diagonal of a morphism of algebraic spaces

The relative diagonal of a morphism of algebraic spaces is representable, locally
of finite type, a monomorphism, separated, and locally quasi-finite in the sense of
Definition 65.5.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.4.1 (1): let `S` be a scheme contained in `Sch_fppf` and let `f : X ⟶ Y`
be a morphism of algebraic spaces over `S`. The relative diagonal morphism
`diagonal f : X ⟶ X ×_Y X` is representable. -/
@[stacks 03HK]
theorem relativelyRepresentable_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : yoneda.relativelyRepresentable (diagonal f) :=
  sorry

/-- Lemma 67.4.1 (2): let `S` be a scheme contained in `Sch_fppf` and let `f : X ⟶ Y`
be a morphism of algebraic spaces over `S`. The relative diagonal morphism
`diagonal f` is locally of finite type in the sense of Definition 65.5.1. -/
@[stacks 03HK]
theorem locallyOfFiniteType_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf (diagonal f) :=
  sorry

/-- Lemma 67.4.1 (3): let `S` be a scheme contained in `Sch_fppf` and let `f : X ⟶ Y`
be a morphism of algebraic spaces over `S`. The relative diagonal morphism
`diagonal f` is a monomorphism in the sense of Definition 65.5.1. -/
@[stacks 03HK]
theorem monomorphisms_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf
      (diagonal f) :=
  sorry

/-- Lemma 67.4.1 (4): let `S` be a scheme contained in `Sch_fppf` and let `f : X ⟶ Y`
be a morphism of algebraic spaces over `S`. The relative diagonal morphism
`diagonal f` is separated in the sense of Definition 65.5.1. -/
@[stacks 03HK]
theorem isSeparated_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf (diagonal f) :=
  sorry

/-- Lemma 67.4.1 (5): let `S` be a scheme contained in `Sch_fppf` and let `f : X ⟶ Y`
be a morphism of algebraic spaces over `S`. The relative diagonal morphism
`diagonal f` is locally quasi-finite in the sense of Definition 65.5.1. -/
@[stacks 03HK]
theorem locallyQuasiFinite_diagonal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf
      (diagonal f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
