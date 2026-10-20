/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Proper-hypercovering families of schemes

This module owns the finite standard proper-surjective chart presentation and
the local refinement predicate used for `ph` coverings.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- A standard `ph` covering of an affine scheme consists of a proper surjective
map together with a finite affine-open cover of its source. -/
structure StandardPhCovering (T : Scheme.{u}) [IsAffine T] where
  /-- The number of affine pieces. -/
  m : ℕ
  /-- The source of the presenting proper surjective morphism. -/
  source : Scheme.{u}
  /-- The proper surjective map to the affine base. -/
  toBase : source ⟶ T
  /-- Properness of the presenting morphism. -/
  isProper_toBase : IsProper toBase
  /-- Surjectivity of the presenting morphism. -/
  surjective_toBase : Surjective toBase
  /-- A finite affine-open cover of the source. -/
  cover : Fin m → source.affineOpens
  /-- The selected affine opens jointly cover the source. -/
  cover_eq_top : ⨆ j, ((cover j : source.Opens)) = ⊤

/-- Construct a standard `ph` covering from a proper surjective morphism and an
explicit finite affine-open cover of its source. -/
def StandardPhCovering.ofAffineOpenCover {T : Scheme.{u}} [IsAffine T]
    (source : Scheme.{u}) (toBase : source ⟶ T)
    (isProper_toBase : IsProper toBase) (surjective_toBase : Surjective toBase)
    (m : ℕ) (cover : Fin m → source.affineOpens)
    (cover_eq_top : ⨆ j, ((cover j : source.Opens)) = ⊤) :
    StandardPhCovering T where
  m := m
  source := source
  toBase := toBase
  isProper_toBase := isProper_toBase
  surjective_toBase := surjective_toBase
  cover := cover
  cover_eq_top := cover_eq_top

/-- The `j`-th affine chart of a standard `ph` covering. -/
abbrev StandardPhCovering.obj {T : Scheme.{u}} [IsAffine T] (Φ : StandardPhCovering T)
    (j : Fin Φ.m) : Scheme.{u} :=
  ((Φ.cover j : Φ.source.Opens)).toScheme

/-- The structure morphism from the `j`-th affine chart to the base scheme. -/
abbrev StandardPhCovering.map {T : Scheme.{u}} [IsAffine T] (Φ : StandardPhCovering T)
    (j : Fin Φ.m) : Φ.obj j ⟶ T :=
  ((Φ.cover j : Φ.source.Opens)).ι ≫ Φ.toBase

/-- Every chart of a standard `ph` covering is affine. -/
theorem StandardPhCovering.isAffine_obj {T : Scheme.{u}} [IsAffine T]
    (Φ : StandardPhCovering T) (j : Fin Φ.m) :
    IsAffine (Φ.obj j) := sorry

/-- The proper, surjective, affine-chart, and covering data of a standard
`ph` covering. -/
theorem StandardPhCovering.source_spec {T : Scheme.{u}} [IsAffine T]
    (Φ : StandardPhCovering T) :
    IsProper Φ.toBase ∧
      Surjective Φ.toBase ∧
        (∀ j, IsAffine (Φ.obj j)) ∧
          (⨆ j, ((Φ.cover j : Φ.source.Opens)) = ⊤) := sorry

/-- A `ph` covering is a locally finite-type family whose pullback to every
affine open admits a standard proper-surjective refinement. -/
class PhCovering {ι : Type v} {T : Scheme.{u}}
    (X : ι → Scheme.{u}) (π : ∀ i, X i ⟶ T) : Prop where
  /-- Every member of the family is locally of finite type. -/
  locallyOfFiniteType : ∀ i, LocallyOfFiniteType (π i)
  /-- Every affine open of the target admits a standard `ph` refinement. -/
  refinesOnAffineOpens :
    ∀ U : T.affineOpens, ∃ Φ : StandardPhCovering U,
      ∀ j : Fin Φ.m, ∃ i : ι, ∃ g : Φ.obj j ⟶ pullback (π i) U.1.ι,
        g ≫ pullback.snd (π i) U.1.ι = Φ.map j

/-- A family is a `ph` covering exactly when its members are locally of finite
type and it admits a standard refinement over every affine open of the target. -/
theorem phCovering_iff {ι : Type v} {T : Scheme.{u}}
    (X : ι → Scheme.{u}) (π : ∀ i, X i ⟶ T) :
    PhCovering X π ↔
      (∀ i, LocallyOfFiniteType (π i)) ∧
        ∀ U : T.affineOpens, ∃ Φ : StandardPhCovering U,
          ∀ j : Fin Φ.m, ∃ i, ∃ g : Φ.obj j ⟶ pullback (π i) U.1.ι,
            g ≫ pullback.snd (π i) U.1.ι = Φ.map j := sorry

/-- Every member of a `ph` covering family is locally of finite type. -/
instance phCoveringLocallyOfFiniteType {ι : Type v} {T : Scheme.{u}}
    {X : ι → Scheme.{u}} {π : ∀ i, X i ⟶ T}
    [h : PhCovering X π] (i : ι) : LocallyOfFiniteType (π i) := sorry

/-- A `ph` covering admits a standard proper-surjective refinement over every
affine open of its target. -/
theorem PhCovering.exists_standardPhRefinement
    {ι : Type v} {T : Scheme.{u}} {X : ι → Scheme.{u}} {π : ∀ i, X i ⟶ T}
    [h : PhCovering X π] (U : T.affineOpens) :
    ∃ Φ : StandardPhCovering U,
      ∀ j : Fin Φ.m, ∃ i : ι, ∃ g : Φ.obj j ⟶ pullback (π i) U.1.ι,
        g ≫ pullback.snd (π i) U.1.ι = Φ.map j := sorry

/-- A proper surjective morphism, regarded as a singleton family, is a `ph` covering. -/
instance phCoveringSingletonOfProperSurjective {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsProper f] [Surjective f] :
    PhCovering (fun _ : PUnit ↦ Y) (fun _ : PUnit ↦ f) := sorry

end AlgebraicGeometry
