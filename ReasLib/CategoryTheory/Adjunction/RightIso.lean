/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Right-adjoint isomorphisms transported across a left-adjoint isomorphism

If two functors are right adjoint to left adjoints identified by a natural isomorphism, this leaf
packages the resulting right-adjoint comparison.  The construction is useful for derived
functors, pushforwards, and tensor/internal-Hom adjunctions, while remaining independent of those
specializations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.Adjunction

section

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable {F F' : C ⥤ D} {G G' : D ⥤ C}

/-- Transporting both adjunctions along a right-adjoint isomorphism and the same left-adjoint
isomorphism recovers the given right-adjoint isomorphism. -/
theorem rightAdjointUniq_ofNatIsoRight_ofNatIsoLeft
    {H : D ⥤ C} (adj : F ⊣ G) (r : G ≅ H) (l : F ≅ F') :
    ((adj.ofNatIsoLeft l).rightAdjointUniq
      ((adj.ofNatIsoRight r).ofNatIsoLeft l)).hom = r.hom := by
  ext X
  apply (((adj.ofNatIsoRight r).ofNatIsoLeft l).homEquiv _ _).symm.injective
  rw [homEquiv_symm_rightAdjointUniq_hom_app]
  rw [homEquiv_ofNatIsoLeft_symm_apply, homEquiv_ofNatIsoRight_symm_apply]
  rw [Iso.hom_inv_id_app, adj.homEquiv_symm_id]
  rfl

/-- If the identity functor is a left adjoint, its counit is the canonical comparison from its
right adjoint to the identity. -/
theorem rightAdjointUniq_id_hom {E : Type u₁} [Category.{v₁} E]
    {J : E ⥤ E} (adj : 𝟭 E ⊣ J) :
    (adj.rightAdjointUniq Adjunction.id).hom = adj.counit := by
  ext X
  have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    adj Adjunction.id X
  change (adj.rightAdjointUniq Adjunction.id).hom.app X ≫ 𝟙 X =
    adj.counit.app X at h
  simpa using h

/-- Successive transports of a left adjoint induce the same right-adjoint comparison as transport
along the composite isomorphism. -/
theorem rightAdjointUniq_ofNatIsoLeft_trans
    {F₂ F₃ : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ G)
    (l : F ≅ F₂) (m : F₂ ≅ F₃) (adj' : F₃ ⊣ H) :
    ((adj.ofNatIsoLeft l).ofNatIsoLeft m).rightAdjointUniq adj' =
      (adj.ofNatIsoLeft (l ≪≫ m)).rightAdjointUniq adj' := by
  apply Iso.ext
  ext X
  apply (adj'.homEquiv _ _).symm.injective
  rw [homEquiv_symm_rightAdjointUniq_hom_app,
    homEquiv_symm_rightAdjointUniq_hom_app]
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.trans_inv]
  exact (Category.assoc _ _ _).symm

/-- Transport a left-adjoint isomorphism across two adjunctions and obtain the corresponding
right-adjoint isomorphism. -/
@[stacks 0FTT "right-derived composite from an identified left adjoint",
  stacks 0FTU "right-derived direct image of a composite",
  stacks 0FTV "derived internal Hom of a tensor composite"]
noncomputable def rightAdjointIsoOfLeftIso
    (e : F ≅ F') (adj : F ⊣ G) (adj' : F' ⊣ G') : G ≅ G' :=
  (adj.ofNatIsoLeft e).rightAdjointUniq adj'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The transported right-adjoint isomorphism is the conjugate of the inverse left-adjoint
isomorphism. -/
theorem rightAdjointIsoOfLeftIso_eq_conjugateIsoEquiv
    (e : F ≅ F') (adj : F ⊣ G) (adj' : F' ⊣ G') :
    rightAdjointIsoOfLeftIso e adj adj' =
      conjugateIsoEquiv adj adj' e.symm := by
  apply Iso.ext
  ext X
  simp only [rightAdjointIsoOfLeftIso, rightAdjointUniq,
    conjugateIsoEquiv_apply_hom, Adjunction.ofNatIsoLeft_counit,
    NatTrans.comp_app, Functor.whiskerLeft_app,
    conjugateEquiv_apply_app]
  simp only [Iso.refl_hom, NatTrans.id_app, Functor.map_id]
  simp [Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The hom-set equivalences commute with `rightAdjointIsoOfLeftIso`. -/
theorem rightAdjointIsoOfLeftIso_homEquiv_apply
    (e : F ≅ F') (adj : F ⊣ G) (adj' : F' ⊣ G')
    (X : C) (Y : D) (f : F'.obj X ⟶ Y) :
    adj.homEquiv X Y (e.hom.app X ≫ f) ≫
        (rightAdjointIsoOfLeftIso e adj adj').hom.app Y =
      adj'.homEquiv X Y f := by
  rw [← Adjunction.homEquiv_ofNatIsoLeft_apply adj e f]
  change (adj.ofNatIsoLeft e).homEquiv X Y f ≫
      ((adj.ofNatIsoLeft e).rightAdjointUniq adj').hom.app Y = _
  apply (adj'.homEquiv X Y).symm.injective
  rw [adj'.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hc := Adjunction.rightAdjointUniq_hom_app_counit
    (adj.ofNatIsoLeft e) adj' Y
  change F'.map (((adj.ofNatIsoLeft e).rightAdjointUniq adj').hom.app Y) ≫
    adj'.counit.app Y = (adj.ofNatIsoLeft e).counit.app Y at hc
  rw [hc]
  rw [← (adj.ofNatIsoLeft e).homEquiv_counit]
  simp

/-- Inverse hom-set equivalences commute with `rightAdjointIsoOfLeftIso`. -/
theorem rightAdjointIsoOfLeftIso_homEquiv_symm_apply
    (e : F ≅ F') (adj : F ⊣ G) (adj' : F' ⊣ G')
    (X : C) (Y : D) (g : X ⟶ G.obj Y) :
    e.hom.app X ≫ (adj'.homEquiv X Y).symm
        (g ≫ (rightAdjointIsoOfLeftIso e adj adj').hom.app Y) =
      (adj.homEquiv X Y).symm g := by
  apply (adj.homEquiv X Y).injective
  rw [Equiv.apply_symm_apply]
  apply (cancel_mono ((rightAdjointIsoOfLeftIso e adj adj').hom.app Y)).1
  rw [rightAdjointIsoOfLeftIso_homEquiv_apply]
  simp

/-- The unit equation characterizing `rightAdjointIsoOfLeftIso`. -/
@[reassoc (attr := simp)]
theorem rightAdjointIsoOfLeftIso_unit_hom
    (e : F ≅ F') (adj : F ⊣ G) (adj' : F' ⊣ G') :
    adj.unit ≫ Functor.whiskerRight e.hom G ≫
        Functor.whiskerLeft F' (rightAdjointIsoOfLeftIso e adj adj').hom =
      adj'.unit := by
  rw [← Category.assoc, ← Adjunction.ofNatIsoLeft_unit]
  exact Adjunction.unit_rightAdjointUniq_hom (adj.ofNatIsoLeft e) adj'

/-- The componentwise unit equation for `rightAdjointIsoOfLeftIso`. -/
@[reassoc (attr := simp)]
theorem rightAdjointIsoOfLeftIso_unit_hom_app
    (e : F ≅ F') (adj : F ⊣ G) (adj' : F' ⊣ G') (X : C) :
    adj.unit.app X ≫ G.map (e.hom.app X) ≫
        (rightAdjointIsoOfLeftIso e adj adj').hom.app (F'.obj X) =
      adj'.unit.app X := by
  have h := NatTrans.congr_app
    (rightAdjointIsoOfLeftIso_unit_hom e adj adj') X
  change adj.unit.app X ≫ G.map (e.hom.app X) ≫
    (rightAdjointIsoOfLeftIso e adj adj').hom.app (F'.obj X) =
      adj'.unit.app X at h
  exact h

/-- The counit equation characterizing `rightAdjointIsoOfLeftIso`. -/
@[reassoc (attr := simp)]
theorem rightAdjointIsoOfLeftIso_hom_counit
    (e : F ≅ F') (adj : F ⊣ G) (adj' : F' ⊣ G') :
    Functor.whiskerRight (rightAdjointIsoOfLeftIso e adj adj').hom F' ≫ adj'.counit =
      Functor.whiskerLeft G e.inv ≫ adj.counit := by
  rw [rightAdjointIsoOfLeftIso, Adjunction.rightAdjointUniq_hom_counit,
    Adjunction.ofNatIsoLeft_counit]

/-- The componentwise counit equation for `rightAdjointIsoOfLeftIso`. -/
@[reassoc (attr := simp)]
theorem rightAdjointIsoOfLeftIso_hom_app_counit
    (e : F ≅ F') (adj : F ⊣ G) (adj' : F' ⊣ G') (X : D) :
    F'.map ((rightAdjointIsoOfLeftIso e adj adj').hom.app X) ≫ adj'.counit.app X =
      e.inv.app (G.obj X) ≫ adj.counit.app X := by
  have h := NatTrans.congr_app
    (rightAdjointIsoOfLeftIso_hom_counit e adj adj') X
  change F'.map ((rightAdjointIsoOfLeftIso e adj adj').hom.app X) ≫
    adj'.counit.app X = e.inv.app (G.obj X) ≫ adj.counit.app X at h
  exact h

/-- The inverse component is the forward comparison obtained from the reversed left-adjoint
isomorphism. -/
theorem rightAdjointIsoOfLeftIso_inv_app
    (e : F ≅ F') (adj : F ⊣ G) (adj' : F' ⊣ G') (X : D) :
    (rightAdjointIsoOfLeftIso e adj adj').inv.app X =
      (rightAdjointIsoOfLeftIso e.symm adj' adj).hom.app X := by
  rw [rightAdjointIsoOfLeftIso_eq_conjugateIsoEquiv,
    rightAdjointIsoOfLeftIso_eq_conjugateIsoEquiv]
  rfl

/-- Successive left-adjoint identifications induce the composite right-adjoint comparison. -/
@[reassoc (attr := simp)]
theorem rightAdjointIsoOfLeftIso_trans
    {F'' : C ⥤ D} {G'' : D ⥤ C}
    (e : F ≅ F') (e' : F' ≅ F'')
    (adj : F ⊣ G) (adj' : F' ⊣ G') (adj'' : F'' ⊣ G'') :
    (rightAdjointIsoOfLeftIso e adj adj').hom ≫
        (rightAdjointIsoOfLeftIso e' adj' adj'').hom =
      (rightAdjointIsoOfLeftIso (e ≪≫ e') adj adj'').hom := by
  rw [rightAdjointIsoOfLeftIso_eq_conjugateIsoEquiv,
    rightAdjointIsoOfLeftIso_eq_conjugateIsoEquiv,
    rightAdjointIsoOfLeftIso_eq_conjugateIsoEquiv]
  change conjugateEquiv adj adj' e.inv ≫
      conjugateEquiv adj' adj'' e'.inv =
    conjugateEquiv adj adj'' ((e ≪≫ e').inv)
  rw [conjugateEquiv_comp]
  rfl

/-- Componentwise transitivity of right-adjoint comparisons transported from the left. -/
@[reassoc (attr := simp)]
theorem rightAdjointIsoOfLeftIso_trans_app
    {F'' : C ⥤ D} {G'' : D ⥤ C}
    (e : F ≅ F') (e' : F' ≅ F'')
    (adj : F ⊣ G) (adj' : F' ⊣ G') (adj'' : F'' ⊣ G'') (X : D) :
    (rightAdjointIsoOfLeftIso e adj adj').hom.app X ≫
        (rightAdjointIsoOfLeftIso e' adj' adj'').hom.app X =
      (rightAdjointIsoOfLeftIso (e ≪≫ e') adj adj'').hom.app X := by
  exact NatTrans.congr_app
    (rightAdjointIsoOfLeftIso_trans e e' adj adj' adj'') X

/-- Transport along the identity left-adjoint isomorphism gives the identity comparison. -/
@[simp]
theorem rightAdjointIsoOfLeftIso_refl (adj : F ⊣ G) :
    (rightAdjointIsoOfLeftIso (Iso.refl F) adj adj).hom = 𝟙 G := by
  rw [rightAdjointIsoOfLeftIso_eq_conjugateIsoEquiv]
  simp

/-- Reversing the left-adjoint isomorphism reverses the transported right-adjoint
isomorphism. -/
@[simp]
theorem rightAdjointIsoOfLeftIso_symm
    (e : F ≅ F') (adj : F ⊣ G) (adj' : F' ⊣ G') :
    rightAdjointIsoOfLeftIso e.symm adj' adj =
      (rightAdjointIsoOfLeftIso e adj adj').symm := by
  rw [rightAdjointIsoOfLeftIso_eq_conjugateIsoEquiv,
    rightAdjointIsoOfLeftIso_eq_conjugateIsoEquiv]
  rfl

end

end CategoryTheory.Adjunction
