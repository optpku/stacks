/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FibrePower.OffDiagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.GlobalSections
public import ReasLib.RepresentationTheory.PermutationSign

/-! # Permutation actions on off-diagonal sections -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Identification `(ρ σ)^* (F|_W) ≅ F|_W` coming from the permutation lying over `X`. -/
noncomputable def offDiagonalRestrictionPastingIso {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Separated f] (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1} ⋙
        etaleRestrictionSheaf (offDiagonalPerm f n σ).hom AddCommGrpCat.{u + 1} ≅
      etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1} :=
  Functor.sheafPushforwardContinuousComp'
    (eqToIso ((etaleRestriction_comp (offDiagonalPerm f n σ).hom
        (offDiagonalToBase f n)).symm.trans
      (by
        have restriction_congr :
            ∀ (a b : offDiagonal f n ⟶ X) (ha : Etale a) (hb : Etale b),
              a = b → @etaleRestriction S _ _ a ha = @etaleRestriction S _ _ b hb := by
          intro a b ha hb hab
          cases hab
          rfl
        exact restriction_congr _ _ inferInstance inferInstance
          (offDiagonalPerm_comp_toBase f n σ))))
    AddCommGrpCat.{u + 1} (smallEtaleTopology (offDiagonal f n))
    (smallEtaleTopology (offDiagonal f n)) (smallEtaleTopology X)

set_option backward.isDefEq.respectTransparency false in
private theorem offDiagonal_constantIntegerPullbackHom_unit {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] :
    toSheafify (smallEtaleTopology U)
        ((Functor.const (smallEtaleSite U)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
        (constantIntegerPullbackHom f).hom =
      Functor.whiskerLeft (etaleRestriction f).op
        (toSheafify (smallEtaleTopology X)
          ((Functor.const (smallEtaleSite X)ᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) := by
  let M : AddCommGrpCat.{u + 1} := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let adj := sheafificationAdjunction (smallEtaleTopology U) AddCommGrpCat.{u + 1}
  have h := (adj.homEquiv ((Functor.const _).obj M)
      ((etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).obj
        (constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X)))).apply_symm_apply
      ((Functor.constCompWhiskeringLeftIso ((smallEtaleSite U)ᵒᵖ)
          (C := AddCommGrpCat.{u + 1}) (etaleRestriction f).op).inv.app M ≫
        Functor.whiskerLeft (etaleRestriction f).op
          (toSheafify (smallEtaleTopology X) ((Functor.const _).obj M)))
  change toSheafify (smallEtaleTopology U) _ ≫ (constantIntegerPullbackHom f).hom = _ at h
  calc
    _ = _ := h
    _ = _ := by
      apply NatTrans.ext
      funext V
      change 𝟙 M ≫ _ = _
      exact Category.id_comp _

section Generic
universe v w z
variable {C : Type v} [Category C] {D : Type w} [Category D] {E : Type z} [Category E]

set_option backward.isDefEq.respectTransparency false in
private theorem offDiagonalWhiskerLeft_comp_eqToHom (A B T : C ⥤ C) (P : Cᵒᵖ ⥤ D) (M : D)
    (w : (Functor.const Cᵒᵖ).obj M ⟶ P)
    (hA : A.op ⋙ P = P) (hB : B.op ⋙ P = P) (hT : T.op ⋙ P = P)
    (hAB : A ⋙ B = T) :
    Functor.whiskerLeft A.op (Functor.whiskerLeft B.op w ≫ eqToHom hB) ≫ eqToHom hA =
      Functor.whiskerLeft T.op w ≫ eqToHom hT := by
  subst T
  rw [Functor.whiskerLeft_comp]
  change (Functor.whiskerLeft (A ⋙ B).op w ≫
      ((Functor.whiskeringLeft _ _ _).obj A.op).map (eqToHom hB)) ≫ eqToHom hA = _
  rw [eqToHom_map, Category.assoc]
  exact congrArg (fun k => Functor.whiskerLeft (A ⋙ B).op w ≫ k)
    (eqToHom_trans _ hA)

private theorem offDiagonalPushforward_eqToIso_hom (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    {A B : C ⥤ D} [A.IsContinuous J K] [B.IsContinuous J K] (p : A = B)
    (F : Sheaf K E) (h : A.op ⋙ F.obj = B.op ⋙ F.obj) :
    ((Functor.sheafPushforwardContinuousIso (eqToIso p) E J K).hom.app F).hom =
      eqToHom h := by
  subst B
  ext V
  simp [Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans]

private theorem offDiagonalWhiskerLeft_id_eqToHom (A : C ⥤ C) (P : Cᵒᵖ ⥤ D) (M : D)
    (w : (Functor.const Cᵒᵖ).obj M ⟶ P) (hA : A.op ⋙ P = P) (hId : A = 𝟭 C) :
    Functor.whiskerLeft A.op w ≫ eqToHom hA = w := by
  subst A
  exact Category.comp_id w
end Generic

set_option backward.isDefEq.respectTransparency false in
private theorem offDiagonalRestriction_comp_eq {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    etaleRestriction (offDiagonalPerm f n σ).hom ⋙ etaleRestriction (offDiagonalToBase f n) =
      etaleRestriction (offDiagonalToBase f n) := by
  have hc : ∀ (a b : offDiagonal f n ⟶ X) (ha : Etale a) (hb : Etale b),
      a = b → @etaleRestriction S _ _ a ha = @etaleRestriction S _ _ b hb := by
    intro a b ha hb hab
    cases hab
    rfl
  exact (etaleRestriction_comp (offDiagonalPerm f n σ).hom
    (offDiagonalToBase f n)).symm.trans
      (hc _ _ inferInstance inferInstance (offDiagonalPerm_comp_toBase f n σ))

set_option backward.isDefEq.respectTransparency false in
private theorem offDiagonalRestriction_presheaf_eq {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ) (σ : Equiv.Perm (Fin n))
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (etaleRestriction (offDiagonalPerm f n σ).hom).op ⋙
        ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F).obj =
      ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F).obj := by
  exact congrArg (fun A => A.op ⋙ F.obj) (offDiagonalRestriction_comp_eq f n σ)

set_option backward.isDefEq.respectTransparency false in
private theorem offDiagonalRestrictionPastingIso_hom {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ) (σ : Equiv.Perm (Fin n))
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (h : (etaleRestriction (offDiagonalPerm f n σ).hom).op ⋙
        ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F).obj =
      ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F).obj) :
    ((offDiagonalRestrictionPastingIso f n σ).hom.app F).hom = eqToHom h := by
  letI := Functor.isContinuous_comp (etaleRestriction (offDiagonalPerm f n σ).hom)
    (etaleRestriction (offDiagonalToBase f n)) (smallEtaleTopology (offDiagonal f n))
    (smallEtaleTopology (offDiagonal f n)) (smallEtaleTopology X)
  unfold offDiagonalRestrictionPastingIso
  dsimp only [Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp]
  rw [Iso.refl_trans]
  apply offDiagonalPushforward_eqToIso_hom

set_option backward.isDefEq.respectTransparency false in
private theorem offDiagonalSectionsPullback_unit {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ) (σ : Equiv.Perm (Fin n))
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (s : constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology (offDiagonal f n)) ⟶
      (etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F) :
    toSheafify (smallEtaleTopology (offDiagonal f n))
        ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
      (constantIntegerPullbackHom (offDiagonalPerm f n σ).hom ≫
        (etaleRestrictionSheaf (offDiagonalPerm f n σ).hom AddCommGrpCat.{u + 1}).map s ≫
        (offDiagonalRestrictionPastingIso f n σ).hom.app F).hom =
      Functor.whiskerLeft (etaleRestriction (offDiagonalPerm f n σ).hom).op
        (toSheafify (smallEtaleTopology (offDiagonal f n))
          ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ s.hom) ≫
        eqToHom (offDiagonalRestriction_presheaf_eq f n σ F) := by
  change toSheafify (smallEtaleTopology (offDiagonal f n)) _ ≫
      (constantIntegerPullbackHom (offDiagonalPerm f n σ).hom).hom ≫
      ((etaleRestrictionSheaf (offDiagonalPerm f n σ).hom AddCommGrpCat.{u + 1}).map s).hom ≫
      ((offDiagonalRestrictionPastingIso f n σ).hom.app F).hom = _
  rw [← Category.assoc, offDiagonal_constantIntegerPullbackHom_unit (offDiagonalPerm f n σ).hom,
    offDiagonalRestrictionPastingIso_hom f n σ F (offDiagonalRestriction_presheaf_eq f n σ F)]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem offDiagonalSectionsPullback_one {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (s : constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology (offDiagonal f n)) ⟶
      (etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F) :
    constantIntegerPullbackHom (offDiagonalPerm f n 1).hom ≫
      (etaleRestrictionSheaf (offDiagonalPerm f n 1).hom AddCommGrpCat.{u + 1}).map s ≫
      (offDiagonalRestrictionPastingIso f n 1).hom.app F = s := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (smallEtaleTopology (offDiagonal f n))
      _ _ ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F).property
  rw [offDiagonalSectionsPullback_unit]
  apply offDiagonalWhiskerLeft_id_eqToHom
  have hc : ∀ (a b : offDiagonal f n ⟶ offDiagonal f n) (ha : Etale a) (hb : Etale b),
      a = b → @etaleRestriction S _ _ a ha = @etaleRestriction S _ _ b hb := by
    intro a b ha hb hab
    cases hab
    rfl
  exact (hc _ _ inferInstance inferInstance
    (congrArg Iso.hom (map_one (offDiagonalPerm f n)))).trans (etaleRestriction_id _)

set_option backward.isDefEq.respectTransparency false in
private theorem offDiagonalSectionsPullback_mul {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (σ τ : Equiv.Perm (Fin n))
    (s : constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology (offDiagonal f n)) ⟶
      (etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F) :
    constantIntegerPullbackHom (offDiagonalPerm f n σ).hom ≫
      (etaleRestrictionSheaf (offDiagonalPerm f n σ).hom AddCommGrpCat.{u + 1}).map
        (constantIntegerPullbackHom (offDiagonalPerm f n τ).hom ≫
          (etaleRestrictionSheaf (offDiagonalPerm f n τ).hom AddCommGrpCat.{u + 1}).map s ≫
          (offDiagonalRestrictionPastingIso f n τ).hom.app F) ≫
      (offDiagonalRestrictionPastingIso f n σ).hom.app F =
    constantIntegerPullbackHom (offDiagonalPerm f n (τ * σ)).hom ≫
      (etaleRestrictionSheaf (offDiagonalPerm f n (τ * σ)).hom AddCommGrpCat.{u + 1}).map s ≫
      (offDiagonalRestrictionPastingIso f n (τ * σ)).hom.app F := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (smallEtaleTopology (offDiagonal f n))
      _ _ ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F).property
  rw [offDiagonalSectionsPullback_unit, offDiagonalSectionsPullback_unit, offDiagonalSectionsPullback_unit]
  apply offDiagonalWhiskerLeft_comp_eqToHom
  have hc : ∀ (a b : offDiagonal f n ⟶ offDiagonal f n) (ha : Etale a) (hb : Etale b),
      a = b → @etaleRestriction S _ _ a ha = @etaleRestriction S _ _ b hb := by
    intro a b ha hb hab
    cases hab
    rfl
  exact (etaleRestriction_comp (offDiagonalPerm f n σ).hom
    (offDiagonalPerm f n τ).hom).symm.trans
      (hc _ _ inferInstance inferInstance
        (congrArg Iso.hom (map_mul (offDiagonalPerm f n) τ σ)).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem offDiagonalSectionsPullback_cancel {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (σ τ : Equiv.Perm (Fin n)) (h : τ * σ = 1)
    (s : constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology (offDiagonal f n)) ⟶
      (etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F) :
    constantIntegerPullbackHom (offDiagonalPerm f n σ).hom ≫
      (etaleRestrictionSheaf (offDiagonalPerm f n σ).hom AddCommGrpCat.{u + 1}).map
        (constantIntegerPullbackHom (offDiagonalPerm f n τ).hom ≫
          (etaleRestrictionSheaf (offDiagonalPerm f n τ).hom AddCommGrpCat.{u + 1}).map s ≫
          (offDiagonalRestrictionPastingIso f n τ).hom.app F) ≫
      (offDiagonalRestrictionPastingIso f n σ).hom.app F = s := by
  let T := fun (ρ : Equiv.Perm (Fin n))
      (s : constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology (offDiagonal f n)) ⟶
        (etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F) =>
    constantIntegerPullbackHom (offDiagonalPerm f n ρ).hom ≫
      (etaleRestrictionSheaf (offDiagonalPerm f n ρ).hom AddCommGrpCat.{u + 1}).map s ≫
      (offDiagonalRestrictionPastingIso f n ρ).hom.app F
  change T σ (T τ s) = s
  calc
    _ = T (τ * σ) s := offDiagonalSectionsPullback_mul f n F σ τ s
    _ = T 1 s := congrArg (fun ρ => T ρ s) h
    _ = s := offDiagonalSectionsPullback_one f n F s

set_option backward.isDefEq.respectTransparency false in
/-- The lifted symmetric-group action on off-diagonal sections by inverse pullback. -/
noncomputable def offDiagonalSectionsAction {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    ULift.{u} (Equiv.Perm (Fin n)) →* Aut
      ((globalSections (offDiagonal f n)).obj
        ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F)) where
  toFun σ :=
    { hom :=
        AddCommGrpCat.ofHom
          { toFun := fun s =>
              constantIntegerPullbackHom (offDiagonalPerm f n σ.down⁻¹).hom ≫
                (etaleRestrictionSheaf (offDiagonalPerm f n σ.down⁻¹).hom
                    AddCommGrpCat.{u + 1}).map s ≫
                  (offDiagonalRestrictionPastingIso f n σ.down⁻¹).hom.app F
            map_zero' := by
              apply Sheaf.hom_ext
              ext V x
              exact map_zero (((offDiagonalRestrictionPastingIso f n σ.down⁻¹).hom.app F).hom.app V).hom
            map_add' := by
              intro s t
              apply Sheaf.hom_ext
              ext V x
              exact map_add (((offDiagonalRestrictionPastingIso f n σ.down⁻¹).hom.app F).hom.app V).hom _ _ }
      inv :=
        AddCommGrpCat.ofHom
          { toFun := fun s =>
              constantIntegerPullbackHom (offDiagonalPerm f n σ.down).hom ≫
                (etaleRestrictionSheaf (offDiagonalPerm f n σ.down).hom
                    AddCommGrpCat.{u + 1}).map s ≫
                  (offDiagonalRestrictionPastingIso f n σ.down).hom.app F
            map_zero' := by
              apply Sheaf.hom_ext
              ext V x
              exact map_zero (((offDiagonalRestrictionPastingIso f n σ.down).hom.app F).hom.app V).hom
            map_add' := by
              intro s t
              apply Sheaf.hom_ext
              ext V x
              exact map_add (((offDiagonalRestrictionPastingIso f n σ.down).hom.app F).hom.app V).hom _ _ }
      hom_inv_id := by
        apply AddCommGrpCat.ext
        intro s
        exact offDiagonalSectionsPullback_cancel f n F σ.down σ.down⁻¹ (inv_mul_cancel _) s
      inv_hom_id := by
        apply AddCommGrpCat.ext
        intro s
        exact offDiagonalSectionsPullback_cancel f n F σ.down⁻¹ σ.down (mul_inv_cancel _) s }
  map_one' := by
    apply Aut.ext
    apply AddCommGrpCat.ext
    intro s
    exact offDiagonalSectionsPullback_one f n F s
  map_mul' := by
    intro σ τ
    apply Aut.ext
    apply AddCommGrpCat.ext
    intro s
    let T := fun (ρ : Equiv.Perm (Fin n))
        (s : constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology (offDiagonal f n)) ⟶
          (etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F) =>
      constantIntegerPullbackHom (offDiagonalPerm f n ρ).hom ≫
        (etaleRestrictionSheaf (offDiagonalPerm f n ρ).hom AddCommGrpCat.{u + 1}).map s ≫
        (offDiagonalRestrictionPastingIso f n ρ).hom.app F
    change T ((σ * τ).down⁻¹) s = T σ.down⁻¹ (T τ.down⁻¹ s)
    calc
      _ = T (τ.down⁻¹ * σ.down⁻¹) s :=
        congrArg (fun ρ => T ρ s) (mul_inv_rev σ.down τ.down)
      _ = _ := (offDiagonalSectionsPullback_mul f n F σ.down⁻¹ τ.down⁻¹ s).symm

/-- The map on `F(W)` induced by a morphism of abelian sheaves on `X_étale`. -/
noncomputable def offDiagonalSectionsMap {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    (globalSections (offDiagonal f n)).obj
        ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F) ⟶
      (globalSections (offDiagonal f n)).obj
        ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj G) :=
  (globalSections (offDiagonal f n)).map
    ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).map φ)

/-- `offDiagonalSectionsMap` is global sections of étale restriction of `φ`. -/
theorem offDiagonalSectionsMap_eq {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    offDiagonalSectionsMap f n φ =
      (globalSections (offDiagonal f n)).map
        ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).map φ) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of abelian sheaves is equivariant for the off-diagonal permutation
action on global sections. -/
theorem offDiagonalSectionsMap_equivariant {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    ∀ g : ULift.{u} (Equiv.Perm (Fin n)),
      (offDiagonalSectionsAction f n F g).hom ≫ offDiagonalSectionsMap f n φ =
        offDiagonalSectionsMap f n φ ≫ (offDiagonalSectionsAction f n G g).hom :=
  by
    intro g
    apply AddCommGrpCat.ext
    intro s
    change
      (constantIntegerPullbackHom (offDiagonalPerm f n g.down⁻¹).hom ≫
          (etaleRestrictionSheaf (offDiagonalPerm f n g.down⁻¹).hom
            AddCommGrpCat.{u + 1}).map s ≫
          (offDiagonalRestrictionPastingIso f n g.down⁻¹).hom.app F) ≫
          (etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).map φ =
        constantIntegerPullbackHom (offDiagonalPerm f n g.down⁻¹).hom ≫
          (etaleRestrictionSheaf (offDiagonalPerm f n g.down⁻¹).hom
            AddCommGrpCat.{u + 1}).map
            (s ≫ (etaleRestrictionSheaf (offDiagonalToBase f n)
              AddCommGrpCat.{u + 1}).map φ) ≫
          (offDiagonalRestrictionPastingIso f n g.down⁻¹).hom.app G
    rw [Functor.map_comp]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg
        (fun k => constantIntegerPullbackHom (offDiagonalPerm f n g.down⁻¹).hom ≫
          (etaleRestrictionSheaf (offDiagonalPerm f n g.down⁻¹).hom
            AddCommGrpCat.{u + 1}).map s ≫ k)
        ((offDiagonalRestrictionPastingIso f n g.down⁻¹).hom.naturality φ).symm

/-- The map on `S_n`-anti-invariants of `F(W)` induced by a morphism of abelian
sheaves. -/
noncomputable def offDiagonalAntiInvariantsMap {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Separated f] (n : ℕ)
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    IntegerCharacter.invariants (offDiagonalSectionsAction f n F) (IntegerCharacter.permutationSign n) ⟶
      IntegerCharacter.invariants (offDiagonalSectionsAction f n G) (IntegerCharacter.permutationSign n) :=
  IntegerCharacter.map (IntegerCharacter.permutationSign n) (offDiagonalSectionsMap f n φ)
    (offDiagonalSectionsMap_equivariant f n φ)

/-- `offDiagonalAntiInvariantsMap` is the equivariant `IntegerCharacter.map` of
`offDiagonalSectionsMap`. -/
theorem offDiagonalAntiInvariantsMap_eq {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    offDiagonalAntiInvariantsMap f n φ =
      IntegerCharacter.map (IntegerCharacter.permutationSign n) (offDiagonalSectionsMap f n φ)
        (offDiagonalSectionsMap_equivariant f n φ) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
