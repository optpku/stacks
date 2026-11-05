/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe w v u

namespace ActualEquivariantTopTrace
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (K : CochainComplex A ℤ) (n : ℤ)

/-- The canonical top homology class enters the lower truncation through
homology -> opcycles. This is an actual map in the ambient category A. -/
def topComponent : K.homology n ⟶ (K.truncGE n).X n :=
  K.homologyι n ≫ (K.truncGEXIsoOpcycles n).inv

/-- The boundary component of the canonical truncation projection. -/
theorem truncationProjection_f :
    (K.πTruncGE n).f n = K.pOpcycles n ≫ (K.truncGEXIsoOpcycles n).inv := by
  dsimp only [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
  rw [ComplexShape.Embedding.liftExtend_f _ _ _ (i := 0) (i' := n) (by simp),
    HomologicalComplex.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv _ _
      (i := 0) (i' := n) (by simp) (by simp [ComplexShape.boundaryGE_embeddingUpIntGE_iff])]
  simp [CochainComplex.truncGEXIsoOpcycles, HomologicalComplex.truncGEXIsoOpcycles]
  rfl

/-- At the lower boundary the incoming differential is zero. Thus the original
opcycle inclusion is also the canonical inclusion of homology through cycles. -/
theorem topComponent_eq_cycles : topComponent K n =
    HomologicalComplex.homologyMap (K.πTruncGE n) n ≫
      ((K.truncGE n).isoHomologyπ (n - 1) n (by simp)
        (by exact ((K.truncGE n).isZero_of_isStrictlyGE n (n - 1) (by lia)).eq_of_src _ _)).inv ≫
      (K.truncGE n).iCycles n := by
  apply (cancel_epi (K.homologyπ n)).1
  simp only [topComponent, ← Category.assoc, HomologicalComplex.homology_π_ι,
    HomologicalComplex.homologyπ_naturality]
  simp only [Category.assoc, HomologicalComplex.isoHomologyπ_hom_inv_id_assoc,
    HomologicalComplex.cyclesMap_i, truncationProjection_f]

theorem topComponent_d (i : ℤ) (hi : (ComplexShape.up ℤ).Rel n i) :
    topComponent K n ≫ (K.truncGE n).d n i = 0 := by
  simp [topComponent_eq_cycles, Category.assoc]

def topInclusion : (CochainComplex.singleFunctor A n).obj (K.homology n) ⟶ K.truncGE n :=
  HomologicalComplex.mkHomFromSingle (topComponent K n) (topComponent_d K n)

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing is a property of the specified complex, not an assumption
that the desired comparison exists. It makes exactly this inclusion a quasi-iso. -/
theorem topInclusion_quasiIso (hvan : ∀ i : ℤ, n < i → IsZero (K.homology i)) :
    QuasiIso (topInclusion K n) := by
  rw [quasiIso_iff]
  intro i
  by_cases hi : i = n
  · subst i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have hmap : HomologicalComplex.homologyMap (topInclusion K n) n =
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n
          (K.homology n)).hom ≫ HomologicalComplex.homologyMap (K.πTruncGE n) n := by
      apply (cancel_epi (((CochainComplex.singleFunctor A n).obj
        (K.homology n)).homologyπ n)).1
      dsimp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
      rw [HomologicalComplex.homologyπ_naturality,
        HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom_assoc]
      apply (cancel_mono ((K.truncGE n).isoHomologyπ (n - 1) n (by simp)
        (by exact ((K.truncGE n).isZero_of_isStrictlyGE n (n - 1) (by lia)).eq_of_src _ _)).inv).1
      apply (cancel_mono ((K.truncGE n).iCycles n)).1
      simp [topInclusion, topComponent_eq_cycles, Category.assoc,
        HomologicalComplex.singleObjCyclesSelfIso_hom]
    rw [hmap]
    letI := K.quasiIsoAt_πTruncGE n n le_rfl
    infer_instance
  · rw [quasiIsoAt_iff_exactAt _ i
      (HomologicalComplex.exactAt_single_obj _ _ _ _ hi)]
    by_cases hni : n ≤ i
    · letI := K.quasiIsoAt_πTruncGE n i hni
      rw [← exactAt_iff_of_quasiIsoAt (K.πTruncGE n) i]
      exact (HomologicalComplex.exactAt_iff_isZero_homology K i).2 (hvan i (by lia))
    · exact (K.truncGE n).exactAt_of_isGE n i (by lia)

variable [HasDerivedCategory.{w} A]

/-- Canonical top-degree trace in D(A), for A including continuous Galois
modules or completed-ring modules. No injectivity of the trace target is required. -/
def map (hvan : ∀ i : ℤ, n < i → IsZero (K.homology i)) {T : A}
    (t : K.homology n ⟶ T) :
    DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj ((CochainComplex.singleFunctor A n).obj T) :=
  -- The quasi-isomorphism is proved from the displayed degree bound.
  letI : QuasiIso (topInclusion K n) := topInclusion_quasiIso K n hvan
  DerivedCategory.Q.map (K.πTruncGE n) ≫
    inv (DerivedCategory.Q.map (topInclusion K n)) ≫
    DerivedCategory.Q.map ((CochainComplex.singleFunctor A n).map t)

end ActualEquivariantTopTrace
