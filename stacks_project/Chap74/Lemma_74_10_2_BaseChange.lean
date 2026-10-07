module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_36_4_Syntomic
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap73.Definition_73_4_1_Precoverage
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage

/-!
# Base change of properties local on the target

This file records that a morphism property of algebraic spaces over a scheme `S`
which is local on the target for the fpqc, fppf, syntomic, smooth, or étale
precoverage is preserved by base change along a single morphism of the
corresponding covering type.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The smooth precoverage on algebraic spaces over `S`: jointly surjective families
of smooth morphisms. -/
abbrev smoothPrecoverage (S : Scheme.{u}) : Precoverage (AlgebraicSpace S) :=
  precoverage (@Smooth S)

/-- The syntomic precoverage on algebraic spaces over `S`: jointly surjective
families of syntomic morphisms. -/
abbrev syntomicPrecoverage (S : Scheme.{u}) : Precoverage (AlgebraicSpace S) :=
  precoverage (@Syntomic S)

/-- An indexed family belongs to `smoothPrecoverage` if and only if each morphism is
smooth and `|X|` equals the union of the images `Points.map (f i)`. -/
theorem ofArrows_mem_smoothPrecoverage_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X) :
    Presieve.ofArrows Xᵢ f ∈ (smoothPrecoverage S).coverings X ↔
      (∀ i, Smooth (f i)) ∧ (⋃ i, Set.range (Points.map (f i))) = Set.univ :=
  sorry

/-- An indexed family belongs to `syntomicPrecoverage` if and only if each morphism
is syntomic and `|X|` equals the union of the images `Points.map (f i)`. -/
theorem ofArrows_mem_syntomicPrecoverage_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X) :
    Presieve.ofArrows Xᵢ f ∈ (syntomicPrecoverage S).coverings X ↔
      (∀ i, Syntomic (f i)) ∧ (⋃ i, Set.range (Points.map (f i))) = Set.univ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.IsLocalAtTarget

variable {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
  {X Y X' Y' : AlgebraicSpace S}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}

/-- An fpqc-local morphism property on the target is preserved by pullback along a
flat morphism. -/
theorem of_isPullback_fpqc
    [P.IsLocalAtTarget (fpqcPrecoverage S)] [Flat g]
    (sq : IsPullback i f' f g) (hf : P f) : P f' :=
  sorry

/-- An fppf-local morphism property on the target is preserved by pullback along a
flat, locally finitely presented morphism. -/
theorem of_isPullback_fppf
    [P.IsLocalAtTarget (fppfPrecoverage S)] [Flat g]
    [LocallyOfFinitePresentation g]
    (sq : IsPullback i f' f g) (hf : P f) : P f' :=
  sorry

/-- A syntomic-local morphism property on the target is preserved by pullback along
a syntomic morphism. -/
theorem of_isPullback_syntomic
    [P.IsLocalAtTarget (syntomicPrecoverage S)] [Syntomic g]
    (sq : IsPullback i f' f g) (hf : P f) : P f' :=
  sorry

/-- A smooth-local morphism property on the target is preserved by pullback along a
smooth morphism. -/
theorem of_isPullback_smooth
    [P.IsLocalAtTarget (smoothPrecoverage S)] [Smooth g]
    (sq : IsPullback i f' f g) (hf : P f) : P f' :=
  sorry

/-- An étale-local morphism property on the target is preserved by pullback along an
étale morphism. -/
theorem of_isPullback_etale
    [P.IsLocalAtTarget etalePrecoverage] [Etale g]
    (sq : IsPullback i f' f g) (hf : P f) : P f' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsLocalAtTarget
