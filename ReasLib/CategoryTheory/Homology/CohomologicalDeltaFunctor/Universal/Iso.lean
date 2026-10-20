/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Universal.Desc
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Iso
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Canonical Isomorphisms of Universal Delta Functors

An isomorphism in degree zero extends canonically to an isomorphism between
universal cohomological delta functors.
-/

noncomputable section

universe vA uA vB uB

namespace CategoryTheory.CohomologicalDeltaFunctor.IsUniversal

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]

/-- The two universal extensions of the inverse degree-zero maps compose to
the identity on the source delta functor. -/
@[simp]
theorem desc_hom_comp_inv {F G : CohomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F.F 0).obj ≅ (G.F 0).obj) :
    Hom.comp (desc e.hom) (desc e.inv) = Hom.id F := sorry

/-- The two universal extensions of the inverse degree-zero maps compose to
the identity on the target delta functor. -/
@[simp]
theorem desc_inv_comp_hom {F G : CohomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F.F 0).obj ≅ (G.F 0).obj) :
    Hom.comp (desc e.inv) (desc e.hom) = Hom.id G := sorry

/-- The canonical isomorphism of universal cohomological delta functors
extending a prescribed degree-zero isomorphism. -/
@[stacks 010U "canonical comparison of universal delta functors"]
noncomputable def iso {F G : CohomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F.F 0).obj ≅ (G.F 0).obj) : HomIso F G where
  hom := desc e.hom
  inv := desc e.inv
  hom_inv_id := desc_hom_comp_inv e
  inv_hom_id := desc_inv_comp_hom e

/-- The canonical comparison with universality supplied as ordinary proof arguments. This form
avoids installing one-off local instances at comparison sites. -/
noncomputable def isoOf {F G : CohomologicalDeltaFunctor A B}
    (hF : IsUniversal F) (hG : IsUniversal G)
    (e : (F.F 0).obj ≅ (G.F 0).obj) : HomIso F G :=
  @iso A _ _ B _ _ F G hF hG e

/-- The degree-zero forward component of `isoOf` is the prescribed forward map. -/
@[simp]
theorem isoOf_hom_app_zero {F G : CohomologicalDeltaFunctor A B}
    (hF : IsUniversal F) (hG : IsUniversal G)
    (e : (F.F 0).obj ≅ (G.F 0).obj) :
    (isoOf hF hG e).hom.app 0 = e.hom := sorry

/-- The degree-zero inverse component of `isoOf` is the prescribed inverse map. -/
@[simp]
theorem isoOf_inv_app_zero {F G : CohomologicalDeltaFunctor A B}
    (hF : IsUniversal F) (hG : IsUniversal G)
    (e : (F.F 0).obj ≅ (G.F 0).obj) :
    (isoOf hF hG e).inv.app 0 = e.inv := sorry

/-- The forward morphism of the canonical universal comparison is the
chosen extension of the degree-zero forward map. -/
@[simp]
theorem iso_hom {F G : CohomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F.F 0).obj ≅ (G.F 0).obj) :
    (iso e).hom = desc e.hom := sorry

/-- The inverse morphism of the canonical universal comparison is the
chosen extension of the degree-zero inverse map. -/
@[simp]
theorem iso_inv {F G : CohomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F.F 0).obj ≅ (G.F 0).obj) :
    (iso e).inv = desc e.inv := sorry

/-- The degree-zero forward component of the canonical universal comparison. -/
@[simp]
theorem iso_hom_app_zero {F G : CohomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F.F 0).obj ≅ (G.F 0).obj) :
    (iso e).hom.app 0 = e.hom := sorry

/-- The degree-zero inverse component of the canonical universal comparison. -/
@[simp]
theorem iso_inv_app_zero {F G : CohomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F.F 0).obj ≅ (G.F 0).obj) :
    (iso e).inv.app 0 = e.inv := sorry

/-- The canonical comparison attached to the identity degree-zero
isomorphism is the identity. -/
@[simp]
theorem iso_refl (F : CohomologicalDeltaFunctor A B) [IsUniversal F] :
    iso (Iso.refl ((F.F 0).obj)) = HomIso.refl F := sorry

/-- Canonical comparisons preserve composition of degree-zero
isomorphisms. -/
@[simp]
theorem iso_trans {F G H : CohomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] [IsUniversal H]
    (e : (F.F 0).obj ≅ (G.F 0).obj) (e' : (G.F 0).obj ≅ (H.F 0).obj) :
    iso (e ≪≫ e') = (iso e).trans (iso e') := sorry

/-- Canonical comparisons preserve symmetry of degree-zero isomorphisms. -/
@[simp]
theorem iso_symm {F G : CohomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F.F 0).obj ≅ (G.F 0).obj) :
    iso e.symm = (iso e).symm := sorry

/-- An isomorphism of universal delta functors with the prescribed
degree-zero forward component is the canonical comparison. -/
theorem iso_unique {F G : CohomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F.F 0).obj ≅ (G.F 0).obj)
    (e' : HomIso F G) (he' : e'.hom.app 0 = e.hom) :
    e' = iso e := sorry

end CategoryTheory.CohomologicalDeltaFunctor.IsUniversal
