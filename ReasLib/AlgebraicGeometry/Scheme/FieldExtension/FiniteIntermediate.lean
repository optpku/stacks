/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction.FlatCompatibility.Composition
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field
public import ReasLib.Topology.Specialization.Dimension

/-!
# Spectra of finite intermediate fields

This module defines the inverse system of spectra of the finite-dimensional intermediate
fields in a field extension, together with its canonical cone and the geometric properties
used by flat base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FieldExtension

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- A finite intermediate field of the extension `K / k`. -/
abbrev FiniteIntermediateField :=
  {L : IntermediateField k K // FiniteDimensional k L}

namespace FiniteIntermediateField

/-- Regard a finite-dimensional intermediate field as a finite intermediate field. -/
def of (L : IntermediateField k K) [FiniteDimensional k L] :
    FiniteIntermediateField k K :=
  ⟨L, inferInstance⟩

/-- The underlying intermediate field of a finite intermediate field. -/
def toIntermediateField (L : FiniteIntermediateField k K) : IntermediateField k K :=
  L.1

/-- The underlying intermediate field of `of L` is `L`. -/
theorem toIntermediateField_of (L : IntermediateField k K) [FiniteDimensional k L] :
    toIntermediateField k K (of k K L) = L := rfl

/-- Inclusion of finite intermediate fields is inclusion of their underlying fields. -/
theorem le_iff (L M : FiniteIntermediateField k K) :
    L ≤ M ↔ toIntermediateField k K L ≤ toIntermediateField k K M := Iff.rfl

end FiniteIntermediateField

/-- The affine scheme associated to a finite intermediate field. -/
abbrev finiteIntermediateSpec (L : FiniteIntermediateField k K) : Scheme.{u} :=
  Spec (CommRingCat.of (L.toIntermediateField k K))

/-- The spectrum map associated to an inclusion of finite intermediate fields. -/
noncomputable def finiteIntermediateSpecMap {L M : FiniteIntermediateField k K}
    (h : L ≤ M) : finiteIntermediateSpec k K M ⟶ finiteIntermediateSpec k K L :=
  Comparison.baseMap (IntermediateField.inclusion h)

/-- The spectrum map associated to an identity inclusion is the identity. -/
theorem finiteIntermediateSpecMap_id (L : FiniteIntermediateField k K) :
    finiteIntermediateSpecMap k K (le_refl L) = 𝟙 (finiteIntermediateSpec k K L) := by
  simpa [finiteIntermediateSpecMap] using
    (Comparison.baseMap_id (k := k) (K := L.toIntermediateField k K))

/-- Spectrum maps associated to inclusions compose contravariantly. -/
theorem finiteIntermediateSpecMap_comp {L M N : FiniteIntermediateField k K}
    (hLM : L ≤ M) (hMN : M ≤ N) :
    finiteIntermediateSpecMap k K hMN ≫ finiteIntermediateSpecMap k K hLM =
      finiteIntermediateSpecMap k K (hLM.trans hMN) := by
  change Comparison.baseMap (IntermediateField.inclusion hMN) ≫
      Comparison.baseMap (IntermediateField.inclusion hLM) =
    Comparison.baseMap (IntermediateField.inclusion (hLM.trans hMN))
  rw [← Comparison.baseMap_comp]
  congr 1

/-- The inverse system of spectra of the finite intermediate fields of `K / k`. -/
noncomputable def finiteIntermediateSpecDiagram :
    OrderDual (FiniteIntermediateField k K) ⥤ Scheme.{u} where
  obj L := finiteIntermediateSpec k K L
  map f := finiteIntermediateSpecMap k K (leOfHom f)
  map_id L := finiteIntermediateSpecMap_id k K L
  map_comp f g :=
    (finiteIntermediateSpecMap_comp k K (leOfHom g) (leOfHom f)).symm

/-- The structure map from a finite intermediate spectrum to `Spec k`. -/
noncomputable def finiteIntermediateStructureMap (L : FiniteIntermediateField k K) :
    finiteIntermediateSpec k K L ⟶ Spec (CommRingCat.of k) :=
  FieldExtension.specMap k L.1

/-- The finite-intermediate-field structure maps are natural. -/
theorem finiteIntermediateStructureMap_naturality
    {L M : OrderDual (FiniteIntermediateField k K)} (f : L ⟶ M) :
    (finiteIntermediateSpecDiagram k K).map f ≫ finiteIntermediateStructureMap k K M =
      finiteIntermediateStructureMap k K L := by
  change Comparison.baseMap (IntermediateField.inclusion (leOfHom f)) ≫
      FieldExtension.specMap k M.1 = FieldExtension.specMap k L.1
  exact Comparison.baseMap_over (IntermediateField.inclusion (leOfHom f))

/-- The inverse system of finite intermediate spectra as schemes over `Spec k`. -/
noncomputable def finiteIntermediateStructure :
    finiteIntermediateSpecDiagram k K ⟶
      (Functor.const (OrderDual (FiniteIntermediateField k K))).obj
        (Spec (CommRingCat.of k)) where
  app L := finiteIntermediateStructureMap k K L
  naturality _ _ f := finiteIntermediateStructureMap_naturality k K f

/-- The canonical map from `Spec K` to a finite intermediate spectrum. -/
noncomputable def finiteIntermediateConeMap (L : FiniteIntermediateField k K) :
    Spec (CommRingCat.of K) ⟶ finiteIntermediateSpec k K L :=
  Spec.map (CommRingCat.ofHom (L.toIntermediateField k K).val)

/-- The canonical maps from `Spec K` to finite intermediate spectra form a cone. -/
theorem finiteIntermediateConeMap_naturality
    {L M : OrderDual (FiniteIntermediateField k K)} (f : L ⟶ M) :
    ((Functor.const (OrderDual (FiniteIntermediateField k K))).obj
          (Spec (CommRingCat.of K))).map f ≫ finiteIntermediateConeMap k K M =
      finiteIntermediateConeMap k K L ≫ (finiteIntermediateSpecDiagram k K).map f := by
  change Spec.map (CommRingCat.ofHom (M.toIntermediateField k K).val.toRingHom) =
    Spec.map (CommRingCat.ofHom (L.toIntermediateField k K).val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (IntermediateField.inclusion (leOfHom f)).toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ : M.toIntermediateField k K →+* K ↦
      Spec.map (CommRingCat.ofHom φ)) (RingHom.ext fun x ↦ rfl)

/-- The cone over the finite-intermediate-spectrum diagram with apex `Spec K`. -/
noncomputable def finiteIntermediateCone : Cone (finiteIntermediateSpecDiagram k K) where
  pt := Spec (CommRingCat.of K)
  π :=
    { app := finiteIntermediateConeMap k K
      naturality := fun _ _ f ↦ finiteIntermediateConeMap_naturality k K f }

/-- For an algebraic extension, the finite-intermediate-spectrum cone is limiting. -/
theorem finiteIntermediateCone_isLimit [Algebra.IsAlgebraic k K] :
    Nonempty (IsLimit (finiteIntermediateCone k K)) := sorry

/-- The finite-intermediate-spectrum cone is compatible with the canonical map to `Spec k`. -/
theorem finiteIntermediateCone_compatible :
    (finiteIntermediateCone k K).π ≫ finiteIntermediateStructure k K =
      (Functor.const (OrderDual (FiniteIntermediateField k K))).map
        (FieldExtension.specMap k K) := by
  ext L
  change Spec.map (CommRingCat.ofHom (L.toIntermediateField k K).val) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (L.toIntermediateField k K))) =
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ : k →+* K ↦ Spec.map (CommRingCat.ofHom φ))
    (RingHom.ext fun x ↦
      IntermediateField.coe_algebraMap_apply (L.toIntermediateField k K) x)

/-- The finite intermediate fields form a nonempty indexing type. -/
theorem finiteIntermediateField_nonempty : Nonempty (FiniteIntermediateField k K) :=
  ⟨⟨⊥, FiniteDimensional.of_finrank_pos (by simp [IntermediateField.finrank_bot])⟩⟩

/-- Finite intermediate fields are directed by inclusion in an algebraic extension. -/
theorem finiteIntermediateField_directed [Algebra.IsAlgebraic k K] :
    IsDirected (FiniteIntermediateField k K) (· ≤ ·) := by
  constructor
  intro L M
  letI : FiniteDimensional k (L.toIntermediateField k K) := L.2
  letI : FiniteDimensional k (M.toIntermediateField k K) := M.2
  let U : FiniteIntermediateField k K :=
    ⟨L.toIntermediateField k K ⊔ M.toIntermediateField k K, inferInstance⟩
  refine ⟨U, ?_, ?_⟩
  · change L.toIntermediateField k K ≤ U.toIntermediateField k K
    exact le_sup_left
  · change M.toIntermediateField k K ≤ U.toIntermediateField k K
    exact le_sup_right

/-- Every spectrum in the finite-intermediate-field diagram is universally catenary. -/
theorem finiteIntermediateDiagram_universallyCatenary :
    ∀ L : OrderDual (FiniteIntermediateField k K),
      UniversallyCatenary ((finiteIntermediateSpecDiagram k K).obj L) :=
  fun L =>
    @AlgebraicGeometry.instUniversallyCatenarySpec
      (L.toIntermediateField k K) _
      (@instUniversallyCatenaryRingOfField.{u, u} (L.toIntermediateField k K) _)

/-- The spectrum map of a field extension is flat. -/
theorem specMap_flat : Flat (FieldExtension.specMap k K) :=
  inferInstance

/-- Every finite-intermediate-field structure map is affine. -/
theorem finiteIntermediateStructureMap_affine :
    ∀ L : FiniteIntermediateField k K,
      IsAffineHom (finiteIntermediateStructureMap k K L) :=
  fun _ => inferInstance

/-- Every finite-intermediate-field structure map is flat. -/
theorem finiteIntermediateStructureMap_flat :
    ∀ L : FiniteIntermediateField k K,
      Flat (finiteIntermediateStructureMap k K L) :=
  fun _ => inferInstance

/-- Every transition map in the finite-intermediate-spectrum diagram is flat. -/
theorem finiteIntermediateTransitionMaps_flat :
    ∀ (L M : FiniteIntermediateField k K) (h : L ≤ M),
      Flat (finiteIntermediateSpecMap k K h) :=
  fun _ _ _ => inferInstance

/-- Every leg of the finite-intermediate-spectrum cone is flat. -/
theorem finiteIntermediateConeMaps_flat :
    ∀ L : FiniteIntermediateField k K,
      Flat (finiteIntermediateConeMap k K L) :=
  fun _ => inferInstance

/-- The constant-zero grading is a dimension function on every finite intermediate spectrum. -/
theorem finiteIntermediateStageDimensions :
    ∀ L : FiniteIntermediateField k K,
      IsDimensionFunction (fun _ : finiteIntermediateSpec k K L ↦ (0 : ℤ)) :=
  fun _ => inferInstance

/-- Constant-zero dimension functions are compatible with finite-intermediate transition maps. -/
theorem finiteIntermediateTransition_compatible
    {L M : FiniteIntermediateField k K} (h : L ≤ M) :
    @Scheme.Hom.IsDimensionFunctionCompatible
      (finiteIntermediateSpec k K L) (finiteIntermediateSpec k K M)
      (finiteIntermediateDiagram_universallyCatenary k K L)
      (finiteIntermediateDiagram_universallyCatenary k K M)
      (finiteIntermediateSpecMap k K h) (finiteIntermediateTransitionMaps_flat k K L M h)
      (fun _ : finiteIntermediateSpec k K L ↦ (0 : ℤ))
      (finiteIntermediateStageDimensions k K L)
      (fun _ : finiteIntermediateSpec k K M ↦ (0 : ℤ))
      (finiteIntermediateStageDimensions k K M) 0 := by
  intro s s' hs'
  simp

/-- The constant-zero dimensions on a finite intermediate spectrum and `Spec K` are
compatible with the canonical cone map. -/
theorem finiteIntermediateConeMap_compatible (L : FiniteIntermediateField k K) :
    @Scheme.Hom.IsDimensionFunctionCompatible
      (finiteIntermediateSpec k K L) (Spec (CommRingCat.of K))
      (finiteIntermediateDiagram_universallyCatenary k K L) inferInstance
      (finiteIntermediateConeMap k K L) (finiteIntermediateConeMaps_flat k K L)
      (fun _ : finiteIntermediateSpec k K L ↦ (0 : ℤ))
      (finiteIntermediateStageDimensions k K L)
      (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ)) inferInstance 0 := by
  intro s s' hs'
  simp

end AlgebraicGeometry.FieldExtension
