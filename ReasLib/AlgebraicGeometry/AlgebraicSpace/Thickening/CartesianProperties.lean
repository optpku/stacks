/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Arrow
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Properties
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Differentials
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.SourceLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Characterization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Factorization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.Cancellation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.Cancellation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction

/-!
# Cartesian morphisms of thickenings of algebraic spaces

If a morphism of thickenings of algebraic spaces over a scheme is cartesian
and both horizontal maps are locally of finite type, then the listed morphism
properties hold for the closed map if and only if they hold for the ambient
map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening.Hom

set_option backward.isDefEq.respectTransparency false

private theorem locallyQuasiFinite_iff_forall_quasiFiniteAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    LocallyQuasiFinite f ↔ ∀ x : Points X, QuasiFiniteAt f x := by
  have h := (locallyQuasiFinite_tfae.{u, u} f).out 0 1
  constructor
  · intro hf x
    obtain ⟨V, i, hi, hx, _, hq⟩ := h.mp ⟨inferInstance, hf⟩ x
    exact ⟨V, i, hi, hx, hq⟩
  · intro hf
    refine (h.mpr ?_).2
    intro x
    obtain ⟨V, i, hi, hx, hq⟩ := hf x
    letI := hi
    exact ⟨V, i, hi, hx, inferInstance, hq⟩

private theorem unramified_iff_of_surjective_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (i : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (j : Y' ⟶ Y) [LocallyOfFiniteType f] [Surjective i]
    (sq : IsPullback i f' f j) : Unramified f' ↔ Unramified f := by
  have hleft := (unramified_tfae.{u, u} f').out 0 1
  have hright := (unramified_tfae.{u, u} f).out 0 1
  rw [hleft, hright]
  constructor
  · intro h x
    obtain ⟨x', rfl⟩ := Surjective.map_surjective (f := i) x
    exact (Unramified.unramifiedAt_iff_of_isPullback i f' f j sq x').mp (h x')
  · intro h x'
    exact (Unramified.unramifiedAt_iff_of_isPullback i f' f j sq x').mpr
      (h (Points.map i x'))

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of
finite type, the closed map is locally quasi-finite if and only if the ambient
map is locally quasi-finite. -/
theorem locallyQuasiFinite_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    LocallyQuasiFinite g.left ↔ LocallyQuasiFinite g.right := by
  letI : IsThickening T.hom := T.prop
  rw [locallyQuasiFinite_iff_forall_quasiFiniteAt,
    locallyQuasiFinite_iff_forall_quasiFiniteAt]
  constructor
  · intro h x
    obtain ⟨x', rfl⟩ := Surjective.map_surjective (f := T.hom) x
    exact (quasiFiniteAt_iff_of_isPullback T.hom g.left g.right U.hom
      hcart.flip x').mp (h x')
  · intro h x'
    exact (quasiFiniteAt_iff_of_isPullback T.hom g.left g.right U.hom
      hcart.flip x').mpr (h (Points.map T.hom x'))

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of
finite type, the closed map is finite if and only if the ambient map is finite. -/
theorem isFinite_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    IsFinite g.left ↔ IsFinite g.right := by
  rw [IsFinite.iff_isIntegralHom, IsFinite.iff_isIntegralHom, isIntegralHom_iff g]

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of
finite type, the closed map is a closed immersion if and only if the ambient
map is a closed immersion. -/
theorem isClosedImmersion_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    IsClosedImmersion g.left ↔ IsClosedImmersion g.right := by
  letI : IsThickening T.hom := T.prop
  rw [IsClosedImmersion.iff_universallyClosed_unramified_universallyInjective,
    IsClosedImmersion.iff_universallyClosed_unramified_universallyInjective,
    universallyClosed_iff g, universallyInjective_iff g,
    unramified_iff_of_surjective_isPullback T.hom g.left g.right U.hom hcart.flip]

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of
finite type, the relative differentials of the closed map vanish if and only if
those of the ambient map vanish. -/
theorem isZero_relativeDifferentials_iff {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    IsZero (Ω[g.left]) ↔ IsZero (Ω[g.right]) := by
  letI : IsThickening T.hom := T.prop
  rw [← Unramified.iff_isZero_relativeDifferentials (f := g.left),
    ← Unramified.iff_isZero_relativeDifferentials (f := g.right)]
  exact unramified_iff_of_surjective_isPullback T.hom g.left g.right U.hom hcart.flip

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of
finite type, the closed map is unramified if and only if the ambient map is
unramified. -/
theorem unramified_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    Unramified g.left ↔ Unramified g.right := by
  letI : IsThickening T.hom := T.prop
  exact unramified_iff_of_surjective_isPullback T.hom g.left g.right U.hom hcart.flip

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of
finite type, the closed map is a monomorphism if and only if the ambient map is
a monomorphism. -/
theorem mono_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    Mono g.left ↔ Mono g.right := by
  calc
    Mono g.left ↔ LocallyOfFiniteType g.left ∧ Mono g.left :=
      (and_iff_right (inferInstance : LocallyOfFiniteType g.left)).symm
    _ ↔ Unramified g.left ∧ UniversallyInjective g.left :=
      (tfae_unramified_mono g.left).out 2 1
    _ ↔ Unramified g.right ∧ UniversallyInjective g.right :=
      and_congr (unramified_iff g hcart) (universallyInjective_iff g)
    _ ↔ LocallyOfFiniteType g.right ∧ Mono g.right :=
      (tfae_unramified_mono g.right).out 1 2
    _ ↔ Mono g.right := and_iff_right (inferInstance : LocallyOfFiniteType g.right)

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of
finite type, the closed map is an immersion if and only if the ambient map is an
immersion. -/
theorem isImmersion_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    IsImmersion g.left ↔ IsImmersion g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  constructor
  · intro h
    letI := h
    obtain ⟨V, c, o, hc, ho, hco⟩ :=
      IsImmersion.exists_closedImmersion_openImmersion_factorization g.left
    letI := hc
    letI := ho
    -- Transport the open part of the factorization across the target thickening.
    have hj := Surjective.map_surjective (f := U.hom)
    have hopen : IsOpenMap (Points.map U.hom) :=
      (IsImmersion.isEmbedding_points U.hom).isInducing.isOpenMap
        (by rw [hj.range_eq]; exact isOpen_univ)
    let W : TopologicalSpace.Opens (Points U.right) :=
      ⟨Points.map U.hom '' Set.range (Points.map o),
        hopen _ (OpenSubspace.isOpen_pointsSet (OpenSubspace.ofι o))⟩
    letI : IsOpenImmersion (OpenSubspace.Construction.ι U.right W) :=
      OpenSubspace.Construction.inclusion_isOpenImmersion U.right W
    have hoW : Set.range (Points.map (o ≫ U.hom)) ⊆ (W : Set (Points U.right)) := by
      rintro _ ⟨v, rfl⟩
      exact ⟨Points.map o v, ⟨v, rfl⟩, (Points.map_comp o U.hom v).symm⟩
    let i : V ⟶ OpenSubspace.Construction.space U.right W :=
      OpenSubspace.Construction.lift (o ≫ U.hom) hoW
    have hi : i ≫ OpenSubspace.Construction.ι U.right W = o ≫ U.hom := rfl
    haveI : IsImmersion i :=
      IsImmersion.of_comp (o ≫ U.hom) (OpenSubspace.Construction.ι U.right W) i hi
    -- The transported inclusion is surjective, hence is a closed immersion.
    have hisurj : Function.Surjective (Points.map i) := by
      intro w
      have hw : Points.map (OpenSubspace.Construction.ι U.right W) w ∈
          (W : Set (Points U.right)) := by
        rw [← OpenSubspace.Construction.inclusion_range U.right W]
        exact ⟨w, rfl⟩
      obtain ⟨_, ⟨v, rfl⟩, hv⟩ := hw
      refine ⟨v, (IsImmersion.isEmbedding_points
        (OpenSubspace.Construction.ι U.right W)).injective ?_⟩
      rw [← Points.map_comp, hi, Points.map_comp]
      exact hv
    haveI : IsClosedImmersion i :=
      IsImmersion.of_isClosed_range_points i
        (by rw [hisurj.range_eq]; exact isClosed_univ)
    have hfW : Set.range (Points.map g.right) ⊆ (W : Set (Points U.right)) := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨t, rfl⟩ := Surjective.map_surjective (f := T.hom) x
      refine ⟨Points.map g.left t, ?_, ?_⟩
      · rw [← hco, Points.map_comp]
        exact ⟨Points.map c t, rfl⟩
      · simpa only [Points.map_comp] using
          congrArg (fun f ↦ Points.map f t) hcart.w
    let f : T.right ⟶ OpenSubspace.Construction.space U.right W :=
      OpenSubspace.Construction.lift g.right hfW
    have hf : f ≫ OpenSubspace.Construction.ι U.right W = g.right := rfl
    have hcf : c ≫ i = T.hom ≫ f := by
      apply (cancel_mono (OpenSubspace.Construction.ι U.right W)).mp
      rw [Category.assoc, hi, Category.assoc, hf, ← Category.assoc, hco]
      exact hcart.w
    haveI : UniversallyClosed c :=
      ((IsClosedImmersion.iff_universallyClosed_unramified_mono c).mp hc).1
    haveI : UniversallyClosed i :=
      ((IsClosedImmersion.iff_universallyClosed_unramified_mono i).mp inferInstance).1
    haveI : UniversallyClosed (T.hom ≫ f) := by
      rw [← hcf]
      infer_instance
    haveI : UniversallyClosed f := UniversallyClosed.of_comp_surjective T.hom f
    haveI : Mono g.right := (mono_iff g hcart).mp inferInstance
    haveI : Mono f := mono_of_mono_fac hf
    haveI : LocallyOfFiniteType (f ≫ OpenSubspace.Construction.ι U.right W) := by
      rw [hf]
      infer_instance
    haveI : LocallyOfFiniteType f :=
      LocallyOfFiniteType.of_comp f (OpenSubspace.Construction.ι U.right W)
    haveI : IsClosedImmersion f :=
      (IsClosedImmersion.iff_universallyClosed_locallyOfFiniteType_mono f).mpr
        ⟨inferInstance, inferInstance, inferInstance⟩
    rw [← hf]
    infer_instance
  · intro h
    exact IsImmersion.of_isPullback hcart.flip h

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of
finite type, the closed map is proper if and only if the ambient map is proper. -/
theorem proper_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    Proper g.left ↔ Proper g.right := by
  constructor
  · intro h
    exact
      { toSeparated := (separated_iff g).mp h.toSeparated
        toFiniteType :=
          { toQuasiCompact := (quasiCompact_iff g).mp h.toFiniteType.toQuasiCompact
            toLocallyOfFiniteType := inferInstance }
        toUniversallyClosed := (universallyClosed_iff g).mp h.toUniversallyClosed }
  · intro h
    exact
      { toSeparated := (separated_iff g).mpr h.toSeparated
        toFiniteType :=
          { toQuasiCompact := (quasiCompact_iff g).mpr h.toFiniteType.toQuasiCompact
            toLocallyOfFiniteType := inferInstance }
        toUniversallyClosed := (universallyClosed_iff g).mpr h.toUniversallyClosed }

end AlgebraicGeometry.AlgebraicSpace.Thickening.Hom
