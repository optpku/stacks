module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.ResidueField

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.Etale.OverField

variable {K : Type u} [Field K] (Y : (Spec (.of K)).Etale)

/-- The specified residue-field spectrum lies over the original ground field. -/
def componentMap (y : Y.left) : Spec (Y.left.residueField y) ⟶ Spec (.of K) :=
  Y.left.fromSpecResidueField y ≫ Y.hom

/-- The coordinate maps of a residue-field component are finite. -/
theorem componentMap_finite_app (y : Y.left) (U : (Spec (.of K)).Opens)
    (hU : IsAffineOpen U) : ((componentMap Y y).app U).hom.Finite := sorry

/-- The affine part is the native affine-spectrum structure; only finiteness is a property law. -/
instance componentMap_isFinite (y : Y.left) : IsFinite (componentMap Y y) where
  toIsAffineHom := inferInstance
  finite_app := componentMap_finite_app Y y

/-- A residue field of an étale scheme over a field is finite separable. -/
instance componentMap_etale (y : Y.left) : Etale (componentMap Y y) := sorry

/-- The actual finite étale residue-field component. -/
def component (y : Y.left) : FiniteEtale (Spec (.of K)) :=
  MorphismProperty.Over.mk _ (componentMap Y y) ⟨inferInstance, inferInstance⟩

/-- The residue-field component inclusion uses the canonical residue-field morphism. -/
def componentι (y : Y.left) : (FiniteEtale.toEtale (Spec (.of K))).obj (component Y y) ⟶ Y :=
  MorphismProperty.Over.homMk (Y.left.fromSpecResidueField y) (by rfl)

/-- Each residue-field inclusion has the native flat-monomorphism open inverse. -/
instance component_isOpenImmersion (y : Y.left) :
    IsOpenImmersion (Y.left.fromSpecResidueField y) := by
  letI : Etale (Y.left.fromSpecResidueField y ≫ Y.hom) := componentMap_etale Y y
  letI : Etale (Y.left.fromSpecResidueField y) :=
    Etale.of_comp (Y.left.fromSpecResidueField y) Y.hom
  exact IsOpenImmersion.of_flat_of_mono (Y.left.fromSpecResidueField y)

/-- The residue-field spectra form a concrete open cover indexed by the actual points. -/
def componentCover : Y.left.OpenCover where
  I₀ := Y.left
  X y := Spec (Y.left.residueField y)
  f y := Y.left.fromSpecResidueField y
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun y ↦ ⟨y, default, Y.left.fromSpecResidueField_apply y default⟩, inferInstance⟩

/-- Descend the actual residue-field inclusions out of their disjoint union. -/
def fromComponents : (∐ fun y : Y.left ↦ Spec (Y.left.residueField y)) ⟶ Y.left :=
  Sigma.desc (fun y ↦ Y.left.fromSpecResidueField y)

instance fromComponents_isOpenImmersion : IsOpenImmersion (fromComponents Y) := by
  apply isOpenImmersion_sigmaDesc
  intro x y hxy
  change Disjoint (Set.range (Y.left.fromSpecResidueField x))
    (Set.range (Y.left.fromSpecResidueField y))
  rw [Scheme.range_fromSpecResidueField, Scheme.range_fromSpecResidueField]
  exact Set.disjoint_singleton.mpr hxy

/-- Every point is covered by its own residue-field spectrum, with a specified preimage. -/
theorem fromComponents_range : Set.range (fromComponents Y) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  refine ⟨Sigma.ι (fun z : Y.left ↦ Spec (Y.left.residueField z)) y default, ?_⟩
  change (Sigma.ι (fun z : Y.left ↦ Spec (Y.left.residueField z)) y ≫ fromComponents Y) default = y
  rw [fromComponents, Sigma.ι_desc]
  exact Y.left.fromSpecResidueField_apply y default

/-- The inverse decomposition map is the native open-immersion lift of the identity. -/
def toComponents : Y.left ⟶ ∐ fun y : Y.left ↦ Spec (Y.left.residueField y) :=
  IsOpenImmersion.lift (fromComponents Y) (𝟙 Y.left)
    (by rw [fromComponents_range Y]; exact Set.subset_univ _)

/-- An étale scheme over a field is the actual disjoint union of its residue-field spectra. -/
def componentsIso : (∐ fun y : Y.left ↦ Spec (Y.left.residueField y)) ≅ Y.left where
  hom := fromComponents Y
  inv := toComponents Y
  hom_inv_id := sorry
  inv_hom_id := sorry

end AlgebraicGeometry.Scheme.Etale.OverField
