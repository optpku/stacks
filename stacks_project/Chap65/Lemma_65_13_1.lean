module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap65.Definition_65_13_2_Separation

/-!
# Properties of the diagonal of an algebraic space

The diagonal of an algebraic space is automatically locally of finite type, a
monomorphism, separated, and locally quasi-finite in the sense of Definition 65.5.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 65.13.1 (1): let `S` be a scheme contained in `Sch_fppf` and let `F` be an
algebraic space over `S`. The diagonal morphism
`diag F : F.functorOfPoints ⟶ F.functorOfPoints ⨯ F.functorOfPoints` is locally of
finite type in the sense of Definition 65.5.1. -/
@[stacks 02X4]
theorem locallyOfFiniteType_diag {S : Scheme.{u}} (F : AlgebraicSpace S) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf (diag F) :=
  sorry

/-- Lemma 65.13.1 (2): let `S` be a scheme contained in `Sch_fppf` and let `F` be an
algebraic space over `S`. The diagonal morphism `diag F` is a monomorphism in the
sense of Definition 65.5.1. -/
@[stacks 02X4]
theorem monomorphisms_diag {S : Scheme.{u}} (F : AlgebraicSpace S) :
    (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf (diag F) :=
  sorry

/-- Lemma 65.13.1 (3): let `S` be a scheme contained in `Sch_fppf` and let `F` be an
algebraic space over `S`. The diagonal morphism `diag F` is separated in the sense of
Definition 65.5.1. -/
@[stacks 02X4]
theorem isSeparated_diag {S : Scheme.{u}} (F : AlgebraicSpace S) :
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf (diag F) :=
  sorry

/-- Lemma 65.13.1 (4): let `S` be a scheme contained in `Sch_fppf` and let `F` be an
algebraic space over `S`. The diagonal morphism `diag F` is locally quasi-finite in
the sense of Definition 65.5.1. -/
@[stacks 02X4]
theorem locallyQuasiFinite_diag {S : Scheme.{u}} (F : AlgebraicSpace S) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf (diag F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
