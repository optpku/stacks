module

public import ReasLib.CategoryTheory.Homology.HomologicalDeltaFunctor.Universal.Desc
public import ReasLib.CategoryTheory.Homology.HomologicalDeltaFunctor.Iso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical Isomorphisms of Universal Homological Delta Functors

An isomorphism in degree zero extends canonically to an isomorphism between universal homological
delta functors.
-/

@[expose] public section

noncomputable section

universe vA uA vB uB

namespace CategoryTheory.HomologicalDeltaFunctor.IsUniversal

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]

/-- The two universal extensions of inverse degree-zero maps compose to the identity. -/
@[simp]
theorem desc_hom_comp_inv {F G : HomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F 0).obj ≅ (G 0).obj) :
    desc e.hom ≫ desc e.inv = 𝟙 F := sorry

/-- The two universal extensions in the opposite order compose to the identity. -/
@[simp]
theorem desc_inv_comp_hom {F G : HomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F 0).obj ≅ (G 0).obj) :
    desc e.inv ≫ desc e.hom = 𝟙 G := sorry

/-- The canonical universal comparison extending a degree-zero isomorphism. -/
@[stacks 010U "canonical comparison of universal homological delta functors"]
noncomputable def iso {F G : HomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F 0).obj ≅ (G 0).obj) : F ≅ G where
  hom := desc e.hom
  inv := desc e.inv
  hom_inv_id := desc_hom_comp_inv e
  inv_hom_id := desc_inv_comp_hom e

/-- The canonical comparison with universality supplied as ordinary proof arguments. -/
noncomputable def isoOf {F G : HomologicalDeltaFunctor A B}
    (hF : IsUniversal F) (hG : IsUniversal G)
    (e : (F 0).obj ≅ (G 0).obj) : F ≅ G :=
  @iso A _ _ B _ _ F G hF hG e

/-- The degree-zero forward component of `isoOf`. -/
@[simp]
theorem isoOf_hom_app_zero {F G : HomologicalDeltaFunctor A B}
    (hF : IsUniversal F) (hG : IsUniversal G)
    (e : (F 0).obj ≅ (G 0).obj) :
    (isoOf hF hG e).hom.app 0 = e.hom := sorry

/-- The degree-zero inverse component of `isoOf`. -/
@[simp]
theorem isoOf_inv_app_zero {F G : HomologicalDeltaFunctor A B}
    (hF : IsUniversal F) (hG : IsUniversal G)
    (e : (F 0).obj ≅ (G 0).obj) :
    (isoOf hF hG e).inv.app 0 = e.inv := sorry

/-- The forward component of the canonical comparison is the chosen extension. -/
@[simp]
theorem iso_hom {F G : HomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F 0).obj ≅ (G 0).obj) :
    (iso e).hom = desc e.hom := sorry

/-- The inverse component of the canonical comparison is the chosen extension. -/
@[simp]
theorem iso_inv {F G : HomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F 0).obj ≅ (G 0).obj) :
    (iso e).inv = desc e.inv := sorry

/-- The degree-zero forward component of the canonical comparison. -/
@[simp]
theorem iso_hom_app_zero {F G : HomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F 0).obj ≅ (G 0).obj) :
    (iso e).hom.app 0 = e.hom := sorry

/-- The degree-zero inverse component of the canonical comparison. -/
@[simp]
theorem iso_inv_app_zero {F G : HomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F 0).obj ≅ (G 0).obj) :
    (iso e).inv.app 0 = e.inv := sorry

/-- The canonical comparison attached to the identity isomorphism is the identity. -/
@[simp]
theorem iso_refl (F : HomologicalDeltaFunctor A B) [IsUniversal F] :
    iso (Iso.refl ((F 0).obj)) = Iso.refl F := sorry

/-- Canonical comparisons preserve composition of degree-zero isomorphisms. -/
@[simp]
theorem iso_trans {F G H : HomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] [IsUniversal H]
    (e : (F 0).obj ≅ (G 0).obj) (e' : (G 0).obj ≅ (H 0).obj) :
    iso (e ≪≫ e') = iso e ≪≫ iso e' := sorry

/-- Canonical comparisons preserve symmetry of degree-zero isomorphisms. -/
@[simp]
theorem iso_symm {F G : HomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F 0).obj ≅ (G 0).obj) :
    iso e.symm = (iso e).symm := sorry

/-- An isomorphism with a prescribed degree-zero component is the canonical comparison. -/
theorem iso_unique {F G : HomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G] (e : (F 0).obj ≅ (G 0).obj)
    (e' : F ≅ G) (he' : e'.hom.app 0 = e.hom) :
    e' = iso e := sorry

/-- Universal homological delta functors that are isomorphic in degree zero are isomorphic in
every degree.  This proposition-valued form is useful when an application has established only
`IsIsomorphic` and has not chosen comparison maps. -/
@[stacks 010U "degreewise uniqueness of universal homological delta functors"]
theorem degree_isomorphic {F G : HomologicalDeltaFunctor A B}
    [IsUniversal F] [IsUniversal G]
    (h₀ : IsIsomorphic (F 0).obj (G 0).obj) (n : ℕ) :
    IsIsomorphic (F n).obj (G n).obj := sorry

end CategoryTheory.HomologicalDeltaFunctor.IsUniversal
