module

public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Closure
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Rational points from residue fields

This file relates the canonical residue-field map of a scheme over a field to sections through
closed points.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.ResidueField

/-- Applying `Spec.map` to the canonical residue-field algebra map over `Spec K` recovers the
structure morphism after the morphism from the residue-field spectrum. -/
theorem specMap_mapOfSpec
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    Spec.map (CommRingCat.ofHom (mapOfSpec f x)) =
      X.fromSpecResidueField x ≫ f := by
  rw [show CommRingCat.ofHom (mapOfSpec f x) =
      CommRingCat.ofHom (algebraMap K (f x).asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (CommRingCat.of K) (f x)).inv ≫
        f.residueFieldMap x by
      rfl]
  rw [Spec.map_comp, Spec.map_comp, Category.assoc,
    Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]

/-- Over an algebraically closed field, a closed point with algebraic residue field admits a
section of the structure morphism whose closed point maps to the given point. -/
theorem exists_section_through_closedPoint_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K]
    (X : AlgebraicGeometry.SchemeOverField K) (x : closedPoints X.left)
    (hx : IsAlgebraicOverSpec X.hom x.1) :
    ∃ g : Spec (CommRingCat.of K) ⟶ X.left,
      g ≫ X.hom = 𝟙 _ ∧ g (IsLocalRing.closedPoint K) = x.1 := by
  -- Local instance justification (defeq pin): use the algebra structure induced by `X.hom`.
  letI : Algebra K (X.left.residueField x.1) := algebraOfSpec X.hom x.1
  have hxIntegral : Algebra.IsIntegral K (X.left.residueField x.1) := hx.isIntegral
  have hbij : Function.Bijective (mapOfSpec X.hom x.1) := by
    -- Local instance justification (proof-local temporary data): expose algebraicity to the bijectivity theorem.
    letI : Algebra.IsIntegral K (X.left.residueField x.1) := hxIntegral
    simpa using
      (IsAlgClosed.algebraMap_bijective_of_isIntegral
        (k := K) (K := X.left.residueField x.1))
  let e : X.left.residueField x.1 ≅ CommRingCat.of K :=
    (RingEquiv.ofBijective (mapOfSpec X.hom x.1) hbij).symm.toCommRingCatIso
  let g : Spec (CommRingCat.of K) ⟶ X.left :=
    Spec.map e.hom ≫ X.left.fromSpecResidueField x.1
  refine ⟨g, ?_, ?_⟩
  · have heInv : e.inv = CommRingCat.ofHom (mapOfSpec X.hom x.1) := rfl
    calc
      g ≫ X.hom = Spec.map e.hom ≫ (X.left.fromSpecResidueField x.1 ≫ X.hom) := by
        simp [g, Category.assoc]
      _ = Spec.map e.hom ≫ Spec.map e.inv := by
        rw [heInv, specMap_mapOfSpec]
      _ = 𝟙 _ := by
        rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  · change X.left.fromSpecResidueField x.1 (Spec.map e.hom (IsLocalRing.closedPoint K)) = x.1
    rw [Spec_closedPoint, Scheme.fromSpecResidueField_apply]

end AlgebraicGeometry.Scheme.Hom.ResidueField
