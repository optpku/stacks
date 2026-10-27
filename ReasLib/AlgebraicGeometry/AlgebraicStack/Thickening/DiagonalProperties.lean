/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Morphism.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyOpen
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Diagonal.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyClosed.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Characterization

/-!
# Relative diagonals of morphisms of thickenings

For a morphism of thickenings of algebraic stacks, each listed morphism
property holds for the relative diagonal of `f` if and only if it holds for
the relative diagonal of `f'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsThickening.Hom

variable {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
variable {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
variable {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- Integrality is equivalent to affineness and universal closedness on
scheme-slice tests. -/
private theorem isIntegralHom_iff_universallyClosed_and_affine (g : X ⟶ Y) :
    AlgebraicStack.IsIntegralHom g ↔
      AlgebraicStack.UniversallyClosed g ∧ Groupoids.Hom.Affine g := by
  constructor
  · intro hint
    refine ⟨(Groupoids.Hom.has_universallyClosed_iff hint.representable).mp ?_,
      ⟨hint.representable, ?_⟩⟩
    · intro U y Fy fy hFy
      exact ((AlgebraicSpace.IsIntegralHom.iff_universallyClosed_and_affine fy).mp
        (hint.has_isIntegralHom y Fy fy hFy)).1
    · intro U y Fy fy hFy
      exact ((AlgebraicSpace.IsIntegralHom.iff_universallyClosed_and_affine fy).mp
        (hint.has_isIntegralHom y Fy fy hFy)).2
  · rintro ⟨hc, ha⟩
    refine ⟨ha.representable, ?_⟩
    intro U y Fy fy hFy
    exact (AlgebraicSpace.IsIntegralHom.iff_universallyClosed_and_affine fy).mpr
      ⟨(Groupoids.Hom.has_universallyClosed_iff ha.representable).mpr hc y Fy fy hFy,
        ha.of_represents y Fy fy hFy⟩

/-- For a locally finite type morphism, finiteness and integrality agree on
all scheme-slice tests. -/
private theorem isFinite_iff_isIntegralHom_of_has_locallyOfFiniteType (g : X ⟶ Y)
    (hg : Groupoids.Hom.has (@AlgebraicSpace.LocallyOfFiniteType S) g) :
    AlgebraicStack.IsFinite g ↔ AlgebraicStack.IsIntegralHom g := by
  constructor
  · intro hfin
    refine ⟨hfin.representable, ?_⟩
    intro U y Fy fy hFy
    letI := hg y Fy fy hFy
    exact (AlgebraicSpace.IsFinite.iff_isIntegralHom fy).mp
      (hfin.has_isFinite y Fy fy hFy)
  · intro hint
    refine ⟨hint.representable, ?_⟩
    intro U y Fy fy hFy
    letI := hg y Fy fy hFy
    exact (AlgebraicSpace.IsFinite.iff_isIntegralHom fy).mpr
      (hint.has_isIntegralHom y Fy fy hFy)

/-- A locally finite type representable morphism is a monomorphism precisely
when it is unramified and universally injective. -/
private theorem mono_iff_unramified_and_universallyInjective (g : X ⟶ Y)
    (hg : Groupoids.Hom.has (@AlgebraicSpace.LocallyOfFiniteType S) g)
    (hrep : relativelyRepresentableByAlgebraicSpaces g) :
    Groupoids.Hom.Mono g ↔
      Groupoids.Hom.has (@AlgebraicSpace.Unramified S) g ∧
        AlgebraicStack.UniversallyInjective g := by
  constructor
  · intro hm
    refine ⟨?_, (Groupoids.Hom.has_universallyInjective_iff hrep).mp ?_⟩
    · intro U y Fy fy hFy
      exact ((AlgebraicSpace.unramified_mono_iff_locallyOfFiniteType_mono fy).mpr
        ⟨hg y Fy fy hFy, hm.of_represents y Fy fy hFy⟩).1
    · intro U y Fy fy hFy
      exact ((AlgebraicSpace.unramified_mono_iff_universallyInjective fy).mp
        ((AlgebraicSpace.unramified_mono_iff_locallyOfFiniteType_mono fy).mpr
          ⟨hg y Fy fy hFy, hm.of_represents y Fy fy hFy⟩)).2
  · rintro ⟨hur, hinj⟩
    refine ⟨hrep, ?_⟩
    intro U y Fy fy hFy
    exact ((AlgebraicSpace.unramified_mono_iff_universallyInjective fy).mpr
      ⟨hur y Fy fy hFy,
        (Groupoids.Hom.has_universallyInjective_iff hrep).mpr hinj y Fy fy hFy⟩).2

/-- A locally finite type representable morphism is a closed immersion
precisely when it is universally closed and a monomorphism. -/
private theorem closedImmersion_iff_universallyClosed_and_mono (g : X ⟶ Y)
    (hg : Groupoids.Hom.has (@AlgebraicSpace.LocallyOfFiniteType S) g)
    (hrep : relativelyRepresentableByAlgebraicSpaces g) :
    Groupoids.Hom.ClosedImmersion g ↔
      AlgebraicStack.UniversallyClosed g ∧ Groupoids.Hom.Mono g := by
  constructor
  · intro hclosed
    refine ⟨(Groupoids.Hom.has_universallyClosed_iff hrep).mp ?_, ⟨hrep, ?_⟩⟩
    · intro U y Fy fy hFy
      exact ((AlgebraicSpace.IsClosedImmersion.iff_universallyClosed_locallyOfFiniteType_mono
        fy).mp (hclosed.of_represents y Fy fy hFy)).1
    · intro U y Fy fy hFy
      exact ((AlgebraicSpace.IsClosedImmersion.iff_universallyClosed_locallyOfFiniteType_mono
        fy).mp (hclosed.of_represents y Fy fy hFy)).2.2
  · rintro ⟨hc, hm⟩
    refine ⟨hrep, ?_⟩
    intro U y Fy fy hFy
    exact (AlgebraicSpace.IsClosedImmersion.iff_universallyClosed_locallyOfFiniteType_mono
      fy).mpr ⟨(Groupoids.Hom.has_universallyClosed_iff hrep).mpr hc y Fy fy hFy,
        hg y Fy fy hFy, hm.of_represents y Fy fy hFy⟩

/-- For a locally finite type representable morphism, properness is equivalent
to separatedness, quasi-compactness, and universal closedness. -/
private theorem has_proper_iff_of_has_locallyOfFiniteType (g : X ⟶ Y)
    (hg : Groupoids.Hom.has (@AlgebraicSpace.LocallyOfFiniteType S) g)
    (hrep : relativelyRepresentableByAlgebraicSpaces g) :
    Groupoids.Hom.has (@AlgebraicSpace.Proper S) g ↔
      Groupoids.Hom.has (@AlgebraicSpace.Separated S) g ∧
        AlgebraicStack.QuasiCompact g ∧ AlgebraicStack.UniversallyClosed g := by
  constructor
  · intro hp
    refine ⟨?_, (Groupoids.Hom.has_quasiCompact_iff hrep).mp ?_,
      (Groupoids.Hom.has_universallyClosed_iff hrep).mp ?_⟩
    · intro U y Fy fy hFy
      exact (hp y Fy fy hFy).toSeparated
    · intro U y Fy fy hFy
      exact (hp y Fy fy hFy).toFiniteType.toQuasiCompact
    · intro U y Fy fy hFy
      exact (hp y Fy fy hFy).toUniversallyClosed
  · rintro ⟨hs, hq, hc⟩
    intro U y Fy fy hFy
    exact
      { toSeparated := hs y Fy fy hFy
        toFiniteType :=
          { toQuasiCompact := (Groupoids.Hom.has_quasiCompact_iff hrep).mpr hq y Fy fy hFy
            toLocallyOfFiniteType := hg y Fy fy hFy }
        toUniversallyClosed :=
          (Groupoids.Hom.has_universallyClosed_iff hrep).mpr hc y Fy fy hFy }

/-- The relative diagonals of a morphism of thickenings are simultaneously
representable by schemes. -/
theorem diagonal_relativelyRepresentable_iff (h : Hom i j f f') :
    FiberedCategoryOver.Groupoids.relativelyRepresentable
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      FiberedCategoryOver.Groupoids.relativelyRepresentable
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
affine. -/
theorem diagonal_affine_iff (h : Hom i j f f') :
    Groupoids.Hom.Affine
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.Affine
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
surjective. -/
theorem diagonal_surjective_iff (h : Hom i j f f') :
    AlgebraicStack.Surjective
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.Surjective
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
quasi-compact. -/
theorem diagonal_quasiCompact_iff (h : Hom i j f f') :
    AlgebraicStack.QuasiCompact
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.QuasiCompact
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
universally closed. -/
theorem diagonal_universallyClosed_iff (h : Hom i j f f') :
    AlgebraicStack.UniversallyClosed
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.UniversallyClosed
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
integral. -/
theorem diagonal_isIntegralHom_iff (h : Hom i j f f') :
    AlgebraicStack.IsIntegralHom
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.IsIntegralHom
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  (isIntegralHom_iff_universallyClosed_and_affine _).trans
    ((and_congr (diagonal_universallyClosed_iff h) (diagonal_affine_iff h)).trans
      (isIntegralHom_iff_universallyClosed_and_affine _).symm)

/-- The relative diagonals of a morphism of thickenings are simultaneously
quasi-separated in the scheme-slice sense. -/
theorem diagonal_quasiSeparated_iff (h : Hom i j f f') :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
separated in the scheme-slice sense. -/
theorem diagonal_separated_iff (h : Hom i j f f') :
    Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
universally injective. -/
theorem diagonal_universallyInjective_iff (h : Hom i j f f') :
    AlgebraicStack.UniversallyInjective
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.UniversallyInjective
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
universally open. -/
theorem diagonal_universallyOpen_iff (h : Hom i j f f') :
    AlgebraicStack.UniversallyOpen
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.UniversallyOpen
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
locally quasi-finite in the scheme-slice sense. -/
theorem diagonal_locallyQuasiFinite_iff (h : Hom i j f f') :
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
finite. -/
theorem diagonal_isFinite_iff (h : Hom i j f f') :
    AlgebraicStack.IsFinite
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      AlgebraicStack.IsFinite
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') := by
  exact (isFinite_iff_isIntegralHom_of_has_locallyOfFiniteType _
    (Groupoids.Hom.has_locallyOfFiniteType_diagonal f)).trans
      ((diagonal_isIntegralHom_iff h).trans
        (isFinite_iff_isIntegralHom_of_has_locallyOfFiniteType _
          (Groupoids.Hom.has_locallyOfFiniteType_diagonal f')).symm)

/-- The relative diagonals of a morphism of thickenings are simultaneously
unramified in the scheme-slice sense. -/
theorem diagonal_unramified_iff (h : Hom i j f f') :
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
monomorphisms. -/
theorem diagonal_mono_iff (h : Hom i j f f') :
    Groupoids.Hom.Mono
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.Mono
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') := by
  exact (mono_iff_unramified_and_universallyInjective _
    (Groupoids.Hom.has_locallyOfFiniteType_diagonal f)
    (Groupoids.Hom.relativelyRepresentableByAlgebraicSpaces_diagonal f)).trans
      ((and_congr (diagonal_unramified_iff h) (diagonal_universallyInjective_iff h)).trans
        (mono_iff_unramified_and_universallyInjective _
          (Groupoids.Hom.has_locallyOfFiniteType_diagonal f')
          (Groupoids.Hom.relativelyRepresentableByAlgebraicSpaces_diagonal f')).symm)

/-- The relative diagonals of a morphism of thickenings are simultaneously
immersions. -/
theorem diagonal_isImmersion_iff (h : Hom i j f f') :
    Groupoids.Hom.Immersion
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.Immersion
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') :=
  sorry

/-- The relative diagonals of a morphism of thickenings are simultaneously
closed immersions. -/
theorem diagonal_isClosedImmersion_iff (h : Hom i j f f') :
    Groupoids.Hom.ClosedImmersion
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.ClosedImmersion
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') := by
  exact (closedImmersion_iff_universallyClosed_and_mono _
    (Groupoids.Hom.has_locallyOfFiniteType_diagonal f)
    (Groupoids.Hom.relativelyRepresentableByAlgebraicSpaces_diagonal f)).trans
      ((and_congr (diagonal_universallyClosed_iff h) (diagonal_mono_iff h)).trans
        (closedImmersion_iff_universallyClosed_and_mono _
          (Groupoids.Hom.has_locallyOfFiniteType_diagonal f')
          (Groupoids.Hom.relativelyRepresentableByAlgebraicSpaces_diagonal f')).symm)

/-- The relative diagonals of a morphism of thickenings are simultaneously
proper in the scheme-slice sense. -/
theorem diagonal_proper_iff (h : Hom i j f f') :
    Groupoids.Hom.has (@AlgebraicSpace.Proper S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f) ↔
      Groupoids.Hom.has (@AlgebraicSpace.Proper S)
        (CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal.{u + 1, u, u + 1} f') := by
  exact (has_proper_iff_of_has_locallyOfFiniteType _
    (Groupoids.Hom.has_locallyOfFiniteType_diagonal f)
    (Groupoids.Hom.relativelyRepresentableByAlgebraicSpaces_diagonal f)).trans
      ((and_congr (diagonal_separated_iff h)
        (and_congr (diagonal_quasiCompact_iff h) (diagonal_universallyClosed_iff h))).trans
          (has_proper_iff_of_has_locallyOfFiniteType _
            (Groupoids.Hom.has_locallyOfFiniteType_diagonal f')
            (Groupoids.Hom.relativelyRepresentableByAlgebraicSpaces_diagonal f')).symm)

end AlgebraicGeometry.AlgebraicStack.IsThickening.Hom
