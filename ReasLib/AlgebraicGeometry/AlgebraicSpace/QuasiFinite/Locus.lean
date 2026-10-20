/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Locality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.BaseChange

/-!
# Quasi-finite locus of a morphism of algebraic spaces

For a locally of finite type morphism of algebraic spaces, the set of points
at which the morphism is quasi-finite is open, and this locus commutes with
base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The set of points at which a locally of finite type morphism of algebraic
spaces is quasi-finite is open. -/
theorem isOpen_quasiFiniteAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] : IsOpen (setOf (QuasiFiniteAt f)) :=
  sorry

/-- In a cartesian square, a locally of finite type morphism is quasi-finite at
the image of a point if and only if the base-changed morphism is quasi-finite
at that point. -/
theorem quasiFiniteAt_iff_of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (x' : Points X') :
    QuasiFiniteAt f' x' ↔ QuasiFiniteAt f (Points.map g' x') :=
  sorry

/-- In a cartesian square, the quasi-finite locus of the base-changed morphism
is the preimage of the original quasi-finite locus. -/
theorem quasiFiniteAt_locus_eq_preimage_of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g) [LocallyOfFiniteType f] :
    setOf (QuasiFiniteAt f') = Points.map g' ⁻¹' setOf (QuasiFiniteAt f) :=
  sorry

/-- The quasi-finite locus of `pullback.snd f g` is the preimage of the
quasi-finite locus of `f` along `pullback.fst f g`. -/
theorem quasiFiniteAt_locus_pullback_snd {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y' ⟶ Y) [HasPullback f g] :
    setOf (QuasiFiniteAt (pullback.snd f g)) =
      Points.map (pullback.fst f g) ⁻¹' setOf (QuasiFiniteAt f) :=
  sorry

/-- The open subspace of points at which a locally finite-type morphism is quasi-finite. -/
noncomputable abbrev quasiFiniteLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] : OpenSubspace X :=
  let W : TopologicalSpace.Opens (Points X) :=
    ⟨setOf (QuasiFiniteAt f), isOpen_quasiFiniteAt f⟩
  { X := OpenSubspace.Construction.space X W
    ι := OpenSubspace.Construction.ι X W
    isOpenImmersion := OpenSubspace.Construction.inclusion_isOpenImmersion X W }

/-- A point lies in the quasi-finite locus if and only if it lies in the
relative-dimension-zero locus. -/
theorem mem_quasiFiniteLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : Points X) :
    x ∈ Set.range (Points.map (quasiFiniteLocus f).ι) ↔ x ∈ fiberDimensionLELocus f 0 :=
  sorry

/-- A point lies in the quasi-finite locus if and only if the morphism has
relative dimension at most zero there. -/
theorem mem_quasiFiniteLocus_iff_relativeDimensionLEAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : Points X) :
    x ∈ Set.range (Points.map (quasiFiniteLocus f).ι) ↔ RelativeDimensionLEAt f 0 x :=
  sorry

/-- A point lies in the quasi-finite locus if and only if the morphism is
quasi-finite at that point. -/
theorem mem_quasiFiniteLocus_iff_quasiFiniteAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : Points X) :
    x ∈ Set.range (Points.map (quasiFiniteLocus f).ι) ↔ QuasiFiniteAt f x :=
  sorry

/-- Any open immersion along which a morphism is locally quasi-finite has
point image contained in its quasi-finite locus. -/
theorem quasiFiniteLocus_maximal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {U : AlgebraicSpace S} (i : U ⟶ X)
    [IsOpenImmersion i] (hf : LocallyQuasiFinite (i ≫ f)) :
    Set.range (Points.map i) ⊆ Set.range (Points.map (quasiFiniteLocus f).ι) :=
  sorry

/-- The quasi-finite locus of a locally quasi-finite morphism contains every point. -/
theorem quasiFiniteLocus_pointsSet_eq_univ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] :
    Set.range (Points.map (quasiFiniteLocus f).ι) = Set.univ :=
  sorry

/-- The quasi-finite locus of a canonical pullback projection is the preimage
of the quasi-finite locus along the other projection. -/
theorem quasiFiniteLocus_pullback_snd {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y' ⟶ Y) [HasPullback f g] :
    Set.range (Points.map (quasiFiniteLocus (pullback.snd f g)).ι) =
      Points.map (pullback.fst f g) ⁻¹'
        Set.range (Points.map (quasiFiniteLocus f).ι) :=
  sorry

/-- Restriction to the quasi-finite locus is locally quasi-finite, and the
relative dimension at every point outside that locus is at least one. -/
theorem locallyQuasiFinite_quasiFiniteLocus {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    LocallyQuasiFinite ((quasiFiniteLocus f).ι ≫ f) ∧
      ∀ x : Points X, x ∉ Set.range (Points.map (quasiFiniteLocus f).ι) →
        (1 : WithBot ℕ∞) ≤ fiberDimensionAt f x :=
  sorry

/-- In any cartesian square, the quasi-finite locus of the base-changed
morphism is the preimage of the original quasi-finite locus. -/
theorem quasiFiniteLocus_pointsSet_eq_preimage_of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g) [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] :
    Set.range (Points.map (quasiFiniteLocus f').ι) =
      Points.map g' ⁻¹' Set.range (Points.map (quasiFiniteLocus f).ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
