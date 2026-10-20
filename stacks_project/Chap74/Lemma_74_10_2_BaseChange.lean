module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalAtTarget.BaseChange

/-!
# Base change of properties local on the target

Typed checks expose the canonical algebraic-space precoverages and base-change
criteria for existing chapter imports.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u v

#check (AlgebraicGeometry.AlgebraicSpace.smoothPrecoverage :
  (S : Scheme.{u}) → Precoverage (AlgebraicSpace S))

#check (AlgebraicGeometry.AlgebraicSpace.syntomicPrecoverage :
  (S : Scheme.{u}) → Precoverage (AlgebraicSpace S))

#check (AlgebraicGeometry.AlgebraicSpace.ofArrows_mem_smoothPrecoverage_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X),
    Presieve.ofArrows Xᵢ f ∈ (smoothPrecoverage S).coverings X ↔
      (∀ i, Smooth (f i)) ∧ (⋃ i, Set.range (Points.map (f i))) = Set.univ)

#check (AlgebraicGeometry.AlgebraicSpace.ofArrows_mem_syntomicPrecoverage_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X),
    Presieve.ofArrows Xᵢ f ∈ (syntomicPrecoverage S).coverings X ↔
      (∀ i, Syntomic (f i)) ∧ (⋃ i, Set.range (Points.map (f i))) = Set.univ)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalAtTarget.of_isPullback_fpqc :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      {X Y X' Y' : AlgebraicSpace S}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}
      [P.IsLocalAtTarget (fpqcPrecoverage S)] [Flat g],
      IsPullback i f' f g → P f → P f')

#check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalAtTarget.of_isPullback_fppf :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      {X Y X' Y' : AlgebraicSpace S}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}
      [P.IsLocalAtTarget (fppfPrecoverage S)] [Flat g]
      [LocallyOfFinitePresentation g],
      IsPullback i f' f g → P f → P f')

#check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalAtTarget.of_isPullback_syntomic :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      {X Y X' Y' : AlgebraicSpace S}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}
      [P.IsLocalAtTarget (syntomicPrecoverage S)] [Syntomic g],
      IsPullback i f' f g → P f → P f')

#check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalAtTarget.of_isPullback_smooth :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      {X Y X' Y' : AlgebraicSpace S}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}
      [P.IsLocalAtTarget (smoothPrecoverage S)] [Smooth g],
      IsPullback i f' f g → P f → P f')

#check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalAtTarget.of_isPullback_etale :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      {X Y X' Y' : AlgebraicSpace S}
      {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}
      [P.IsLocalAtTarget etalePrecoverage] [Etale g],
      IsPullback i f' f g → P f → P f')

