/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback

/-!
# Pushforward adjunctions for presheaves of modules

This module supplies the module-valued lift of an adjunction between indexing categories. The
construction is independent of topological spaces and belongs with the presheaf-module
pushforward API.
-/

@[expose] public section

/-!
# Pushforward–pushforward adjunction for presheaves of modules

This is the presheaf-of-modules analogue of `SheafOfModules.pushforwardPushforwardAdj`
(`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`).  Given an adjunction
`adj : F ⊣ G` between the index categories together with compatible morphisms of presheaves of
rings `φ : S ⟶ F.op ⋙ R` and `ψ : R ⟶ G.op ⋙ S`, the pushforward functors along `φ` and `ψ`
are themselves adjoint.
-/

open CategoryTheory

universe v v₁ v₂ u₁ u₂ u

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section Congr

variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}

/-- The objectwise comparison for pushforwards along equal ring maps.  Its section map is the
identity, while `ModuleCat.restrictScalarsCongr` records the scalar-map transport. -/
@[stacks 01FD "objectwise pushforward congruence"]
noncomputable def pushforwardCongrApp {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ)
    (M : PresheafOfModules R) :
    (pushforward.{v} φ).obj M ≅ (pushforward.{v} ψ).obj M :=
  e ▸ Iso.refl ((pushforward.{v} φ).obj M)

/-- The forward natural transformation for the objectwise pushforward congruences. -/
@[stacks 01FD "forward pushforward congruence natural transformation"]
noncomputable def pushforwardCongrNatTrans {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) :
    pushforward.{v} φ ⟶ pushforward.{v} ψ where
  app M := (pushforwardCongrApp e M).hom
  naturality {M N} f := sorry

/-- Naturality of the forward pushforward congruence in the module presheaf. -/
@[stacks 01FD "forward pushforward congruence naturality"]
theorem pushforwardCongrNatTrans_naturality {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ)
    {M N : PresheafOfModules R} (f : M ⟶ N) :
    (pushforward.{v} φ).map f ≫ (pushforwardCongrNatTrans e).app N =
      (pushforwardCongrNatTrans e).app M ≫ (pushforward.{v} ψ).map f := sorry

/-- The inverse natural transformation for the objectwise pushforward congruences. -/
@[stacks 01FD "inverse pushforward congruence natural transformation"]
noncomputable def pushforwardCongrInvNatTrans {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) :
    pushforward.{v} ψ ⟶ pushforward.{v} φ where
  app M := (pushforwardCongrApp e M).inv
  naturality {M N} f := sorry

/-- Naturality of the inverse pushforward congruence in the module presheaf. -/
@[stacks 01FD "inverse pushforward congruence naturality"]
theorem pushforwardCongrInvNatTrans_naturality {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ)
    {M N : PresheafOfModules R} (f : M ⟶ N) :
    (pushforward.{v} ψ).map f ≫ (pushforwardCongrInvNatTrans e).app N =
      (pushforwardCongrInvNatTrans e).app M ≫ (pushforward.{v} φ).map f := sorry

/-- The forward pushforward congruence followed by its inverse is the identity natural
transformation. -/
@[simp, stacks 01FD "pushforward congruence forward-inverse law"]
theorem pushforwardCongrNatTrans_hom_inv_id {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) :
    pushforwardCongrNatTrans e ≫ pushforwardCongrInvNatTrans e = 𝟙 _ := sorry

/-- The inverse pushforward congruence followed by its forward map is the identity natural
transformation. -/
@[simp, stacks 01FD "pushforward congruence inverse-forward law"]
theorem pushforwardCongrNatTrans_inv_hom_id {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) :
    pushforwardCongrInvNatTrans e ≫ pushforwardCongrNatTrans e = 𝟙 _ := sorry

/-- Pushforward along equal morphisms of presheaves of rings gives a literal natural isomorphism.
The forward and inverse transformations are owned explicitly for downstream reuse. -/
@[stacks 01FD "pushforward congruence natural isomorphism"]
noncomputable def pushforwardCongr {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) :
    pushforward.{v} φ ≅ pushforward.{v} ψ where
  hom := pushforwardCongrNatTrans e
  inv := pushforwardCongrInvNatTrans e
  hom_inv_id := pushforwardCongrNatTrans_hom_inv_id e
  inv_hom_id := pushforwardCongrNatTrans_inv_hom_id e

/-- The forward natural transformation of `pushforwardCongr`. -/
@[simp, stacks 01FD "pushforward congruence hom"]
theorem pushforwardCongr_hom {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) :
    (pushforwardCongr e).hom = pushforwardCongrNatTrans e := sorry

/-- The inverse natural transformation of `pushforwardCongr`. -/
@[simp, stacks 01FD "pushforward congruence inverse"]
theorem pushforwardCongr_inv {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) :
    (pushforwardCongr e).inv = pushforwardCongrInvNatTrans e := sorry

/-- The module-presheaf component of `pushforwardCongr` is the named objectwise comparison. -/
@[simp, stacks 01FD "pushforward congruence component"]
theorem pushforwardCongr_app {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ)
    (M : PresheafOfModules R) :
    (pushforwardCongr e).app M = pushforwardCongrApp e M := sorry

/-- A forward component of `pushforwardCongr` is the named forward comparison. -/
@[simp, stacks 01FD "pushforward congruence hom component"]
theorem pushforwardCongr_hom_app {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ)
    (M : PresheafOfModules R) :
    (pushforwardCongr e).hom.app M = (pushforwardCongrNatTrans e).app M := sorry

/-- An inverse component of `pushforwardCongr` is the named inverse comparison. -/
@[simp, stacks 01FD "pushforward congruence inverse component"]
theorem pushforwardCongr_inv_app {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ)
    (M : PresheafOfModules R) :
    (pushforwardCongr e).inv.app M = (pushforwardCongrInvNatTrans e).app M := sorry

/-- The forward comparison between pushforwards along equal ring maps is the identity on
underlying sections. -/
@[simp, stacks 01FD "pushforward congruence forward section map"]
lemma pushforwardCongr_hom_app_app_apply {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) (M X x) :
    (((pushforwardCongr e).hom.app M).app X).hom x = x := sorry

/-- The inverse comparison between pushforwards along equal ring maps is the identity on
underlying sections. -/
@[simp, stacks 01FD "pushforward congruence inverse section map"]
lemma pushforwardCongr_inv_app_app_apply {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) (M X x) :
    (((pushforwardCongr e).inv.app M).app X).hom x = x := sorry

/-- The forward named natural transformation acts as the identity on sections. -/
@[simp, stacks 01FD "pushforward congruence natural transformation section map"]
lemma pushforwardCongrNatTrans_app_app_apply {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) (M X x) :
    (((pushforwardCongrNatTrans e).app M).app X).hom x = x := sorry

/-- The inverse named natural transformation acts as the identity on sections. -/
@[simp, stacks 01FD "inverse pushforward congruence natural transformation section map"]
lemma pushforwardCongrInvNatTrans_app_app_apply {φ ψ : S ⟶ F.op ⋙ R} (e : φ = ψ) (M X x) :
    (((pushforwardCongrInvNatTrans e).app M).app X).hom x = x := sorry

end Congr

section NatTrans

variable {F G : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}
  (φ : S ⟶ G.op ⋙ R)

set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation `α : F ⟶ G` gives a natural transformation between the pushforward
functors `pushforward φ ⟶ pushforward (φ ≫ Functor.whiskerRight (NatTrans.op α) R)`. -/
noncomputable def pushforwardNatTrans (α : F ⟶ G) :
    pushforward.{v} φ ⟶ pushforward.{v} (φ ≫ Functor.whiskerRight (NatTrans.op α) R) where
  app M :=
    { app X := (ModuleCat.restrictScalars (φ.app X).hom).map (M.map (α.app X.unop).op)
      naturality := fun {X Y} i => by
        ext x
        change (M.presheaf.map (G.map i.unop).op ≫ M.presheaf.map (α.app Y.unop).op) _ =
          (M.presheaf.map (α.app X.unop).op ≫ M.presheaf.map (F.map i.unop).op) _
        simp only [← CategoryTheory.Functor.map_comp, ← op_comp, α.naturality] }
  naturality {M N} f := by
    ext X x
    exact (congr($((f.naturality (α.app X.unop).op)) x)).symm

/-- The component of `pushforwardNatTrans φ α` acts by the restriction map indexed by
`α.app X.unop`. -/
lemma pushforwardNatTrans_app_app_apply (α : F ⟶ G) (M) (X) (x) :
    (((pushforwardNatTrans φ α).app M).app X).hom x = M.map (α.app X.unop).op x := rfl

end NatTrans

section Adjunction

variable {F : C ⥤ D} {G : D ⥤ C}
  {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}
  (adj : F ⊣ G)
  (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ S)
  (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) R = ψ ≫ G.op.whiskerLeft φ)
  (H₂ : φ ≫ F.op.whiskerLeft ψ ≫ Functor.whiskerRight (NatTrans.op adj.unit) S = 𝟙 S)

set_option backward.isDefEq.respectTransparency false in
/-- If `F ⊣ G`, then the pushforwards along compatible ring morphisms `φ`, `ψ` are also adjoint. -/
noncomputable def pushforwardPushforwardAdj : pushforward.{v} φ ⊣ pushforward.{v} ψ where
  unit :=
    (pushforwardId _).inv ≫ pushforwardNatTrans (𝟙 _) adj.counit ≫
      (pushforwardCongr (by simpa using H₁)).hom ≫ (pushforwardComp _ _).inv
  counit :=
    (pushforwardComp _ _).hom ≫ pushforwardNatTrans _ adj.unit ≫
      (pushforwardCongr (by simpa using H₂)).hom ≫ (pushforwardId _).hom
  left_triangle_components M := sorry
  right_triangle_components M := sorry

/-- The unit of `pushforwardPushforwardAdj` acts on sections through the counit of the indexing
adjunction. -/
lemma pushforwardPushforwardAdj_unit_app_app_apply (M) (X) (x) :
    (((pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M).app X).hom x =
      M.map (adj.counit.app X.unop).op x := sorry

/-- The counit of `pushforwardPushforwardAdj` acts on sections through the unit of the indexing
adjunction. -/
lemma pushforwardPushforwardAdj_counit_app_app_apply (M) (X) (x) :
    (((pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app M).app X).hom x =
      M.map (adj.unit.app X.unop).op x := sorry

end Adjunction

end PresheafOfModules
