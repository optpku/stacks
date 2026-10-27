/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- The power of the ideal sheaf defining the canonical closed factor of an immersion that
defines its `n`th infinitesimal neighbourhood. -/
def ideal (n : ℕ) : i.coborderRange.toScheme.IdealSheafData :=
  i.liftCoborder.ker ^ (n + 1)

/-- The ideal defining an infinitesimal neighbourhood is pointwise the corresponding power
of the ideal of the canonical closed factor. -/
theorem ideal_apply (n : ℕ) (U : i.coborderRange.toScheme.affineOpens) :
    (ideal i n).ideal U = (i.liftCoborder.ker.ideal U) ^ (n + 1) := rfl

/-- The `n`th infinitesimal neighbourhood of the source of an immersion inside its canonical
open coborder. -/
def scheme (n : ℕ) : Scheme.{u} :=
  (ideal i n).subscheme

/-- The infinitesimal-neighbourhood scheme is the subscheme defined by the corresponding
power of the immersion ideal. -/
theorem scheme_eq_subscheme (n : ℕ) :
    scheme i n = (ideal i n).subscheme := rfl

/-- The canonical morphism from an infinitesimal neighbourhood to the ambient scheme. -/
def toAmbient (n : ℕ) : scheme i n ⟶ X :=
  (ideal i n).subschemeι ≫ i.coborderRange.ι

/-- The canonical morphism from the source of an immersion to its `n`th infinitesimal
neighbourhood. -/
def fromSource (n : ℕ) : Z ⟶ scheme i n :=
  i.liftCoborder.toImage ≫ Scheme.IdealSheafData.inclusion
    (fun _ ↦ Ideal.pow_le_self (Nat.succ_ne_zero n))

set_option backward.isDefEq.respectTransparency false in
/-- The source morphism followed by the closed-subscheme inclusion recovers the canonical
closed factor of the immersion. -/
theorem fromSource_subschemeι (n : ℕ) :
    fromSource i n ≫ (ideal i n).subschemeι = i.liftCoborder := by
  simp [fromSource, ideal]

set_option backward.isDefEq.respectTransparency false in
/-- The infinitesimal-neighbourhood factorization recovers the original immersion. -/
theorem fromSource_toAmbient (n : ℕ) :
    fromSource i n ≫ toAmbient i n = i := by
  rw [toAmbient, ← Category.assoc, fromSource_subschemeι, Scheme.Hom.liftCoborder_ι]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from the source to its infinitesimal neighbourhood is a closed
immersion. -/
instance fromSource_isClosedImmersion (n : ℕ) : IsClosedImmersion (fromSource i n) := by
  have : IsClosedImmersion (fromSource i n ≫ (ideal i n).subschemeι) := by
    rw [fromSource_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (ideal i n).subschemeι

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from an infinitesimal neighbourhood to the ambient scheme is an
immersion. -/
instance toAmbient_isImmersion (n : ℕ) : IsImmersion (toAmbient i n) := by
  dsimp [toAmbient]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The source and its infinitesimal neighbourhood have the same underlying topological
space. -/
theorem surjective_fromSource (n : ℕ) : Function.Surjective (fromSource i n) := by
  intro x
  have hx : (ideal i n).subschemeι x ∈ i.liftCoborder.ker.support := by
    simpa [ideal] using (ideal i n).range_subschemeι.le ⟨x, rfl⟩
  have hsupport : (i.liftCoborder.ker.support : Set i.coborderRange.toScheme) =
      Set.range i.liftCoborder :=
    i.liftCoborder.support_ker.trans
      i.liftCoborder.isClosedEmbedding.isClosed_range.closure_eq
  obtain ⟨z, hz⟩ : (ideal i n).subschemeι x ∈ Set.range i.liftCoborder := hsupport ▸ hx
  refine ⟨z, (ideal i n).subschemeι.isClosedEmbedding.injective ?_⟩
  change (fromSource i n ≫ (ideal i n).subschemeι) z = _
  rw [fromSource_subschemeι]
  exact hz

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the source map to its `n`th infinitesimal neighbourhood has vanishing
`(n + 1)`st power. -/
theorem ker_fromSource_pow_succ (n : ℕ) :
    (fromSource i n).ker ^ (n + 1) = ⊥ := by
  let g := (ideal i n).subschemeι
  have hmap : (fromSource i n).ker.map g = i.liftCoborder.ker := by
    rw [Scheme.IdealSheafData.map_ker, fromSource_subschemeι]
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : i.coborderRange.toScheme.affineOpens ↦ ⟨g ⁻¹ᵁ U, U.2.preimage g⟩)
    (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top _)) ?_
  intro U
  have hker :
      ((fromSource i n).ker.ideal ⟨_, U.2.preimage g⟩).comap (g.app U).hom =
        i.liftCoborder.ker.ideal U := by
    rw [← Scheme.IdealSheafData.ideal_map_of_isAffineHom, hmap]
  have hquot :
      (fromSource i n).ker.ideal ⟨_, U.2.preimage g⟩ =
        (i.liftCoborder.ker.ideal U).map (g.app U).hom := by
    rw [← hker, Ideal.map_comap_of_surjective _ (g.app_surjective U U.2)]
  change ((fromSource i n).ker.ideal ⟨_, U.2.preimage g⟩) ^ (n + 1) = ⊥
  rw [hquot, ← Ideal.map_pow]
  apply (Ideal.map_eq_bot_iff_le_ker _).mpr
  rw [(ideal i n).ker_subschemeι_app]
  exact le_rfl

/-- The canonical map from an immersion to its `n`th infinitesimal neighbourhood is an
`n`th-order thickening. -/
instance fromSource_isNthOrderThickening (n : ℕ) :
    IsNthOrderThickening n (fromSource i n) where
  isClosedImmersion := inferInstance
  ker_isNilpotent := ⟨n + 1, by simpa using ker_fromSource_pow_succ i n⟩
  ker_pow_succ := by simpa using ker_fromSource_pow_succ i n

end AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood
