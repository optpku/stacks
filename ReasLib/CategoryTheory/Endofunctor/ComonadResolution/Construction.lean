/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.Generators
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0G5N

# Canonical simplicial resolutions of comonads

This leaf makes the generated resolution canonical: it is functorial in the Mathlib `Comonad`,
carries a realization witness, and is canonically isomorphic to every realization of the same
iterated-endofunctor formulas.
-/

@[expose] public section

open Opposite
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Augmentation
open CategoryTheory.Functor
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Comonad

variable (G : Comonad C)

/-- A simplicial endofunctor object realizes the iterated resolution formulas of `G`. -/
@[stacks 0G5N "comonad resolution realization predicate"]
abbrev Realizes (G : Comonad C) (U : SimplicialObject (C ⥤ C)) : Prop :=
  EndofunctorResolution.Realization G.ε G.δ U

/-- The right counit identity in the iterated-endofunctor presentation of a comonad. -/
@[stacks 0G5N "comonad resolution right counit"]
theorem simplicialResolution.right_counit :
    IteratedEndofunctor.degeneracy G.δ 0 0 ≫
      IteratedEndofunctor.face G.ε 0 0 = 𝟙 G.toFunctor := by
  ext X
  change G.δ.app X ≫ (G.map (G.ε.app X) ≫ 𝟙 _) = 𝟙 _
  simpa only [Category.comp_id] using G.right_counit X

/-- The left counit identity in the iterated-endofunctor presentation of a comonad. -/
@[stacks 0G5N "comonad resolution left counit"]
theorem simplicialResolution.left_counit :
    IteratedEndofunctor.degeneracy G.δ 0 0 ≫
      IteratedEndofunctor.face G.ε 0 1 = 𝟙 G.toFunctor := by
  ext X
  change G.δ.app X ≫ (G.ε.app (G.obj X) ≫ 𝟙 _) = 𝟙 _
  simpa only [Category.comp_id] using G.left_counit X

/-- Coassociativity in the iterated-endofunctor presentation of a comonad. -/
@[stacks 0G5N "comonad resolution coassociativity"]
theorem simplicialResolution.coassoc :
    IteratedEndofunctor.degeneracy G.δ 0 0 ≫
        IteratedEndofunctor.degeneracy G.δ 1 0 =
      IteratedEndofunctor.degeneracy G.δ 0 0 ≫
        IteratedEndofunctor.degeneracy G.δ 1 1 := by
  ext X
  change G.δ.app X ≫ G.map (G.δ.app X) =
    G.δ.app X ≫ (G.δ.app (G.obj X) ≫ 𝟙 _)
  simpa only [Category.comp_id] using G.coassoc X

/-- The canonical simplicial resolution of a comonad. -/
@[stacks 0G5N]
noncomputable def simplicialResolution : SimplicialObject (C ⥤ C) :=
  EndofunctorResolution.simplicial.resolution G.ε G.δ
    (simplicialResolution.right_counit G) (simplicialResolution.left_counit G)
    (simplicialResolution.coassoc G)

/-- The degree-`n` term of the canonical comonad resolution is the positive `(n + 1)`-fold
iterate of its underlying endofunctor. -/
@[simp, stacks 0G5N "canonical comonad resolution object formula"]
theorem simplicialResolution.obj (Δ : SimplexCategoryᵒᵖ) :
    G.simplicialResolution.obj Δ = G.toFunctor ⁺⦋Δ.unop.len⦌ := by
  rfl

/-- The canonical comonad resolution evaluates a simplex morphism by its generator code. -/
@[simp, stacks 0G5N "canonical comonad resolution map formula"]
theorem simplicialResolution.map {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') :
    G.simplicialResolution.map θ =
      EndofunctorResolution.simplicial.map G.ε G.δ θ := by
  rfl

/-- Faces in the canonical comonad resolution insert the counit. -/
@[simp, stacks 0G5N "canonical comonad resolution face formula"]
theorem simplicialResolution.face {n : ℕ} (i : Fin (n + 2)) :
    G.simplicialResolution.δ i =
      IteratedEndofunctor.face G.ε n i := by
  set_option backward.isDefEq.respectTransparency false in
    change EndofunctorResolution.simplicial.map G.ε G.δ (SimplexCategory.δ i).op =
      IteratedEndofunctor.face G.ε n i
    have h := (EndofunctorResolution.simplicial.resolution.realization G.ε G.δ
      (simplicialResolution.right_counit G) (simplicialResolution.left_counit G)
      (simplicialResolution.coassoc G)).δ_eq i
    change 𝟙 _ ≫ IteratedEndofunctor.face G.ε n i =
      EndofunctorResolution.simplicial.map G.ε G.δ (SimplexCategory.δ i).op ≫ 𝟙 _ at h
    simpa only [Category.id_comp, Category.comp_id] using h.symm

/-- Degeneracies in the canonical comonad resolution insert the comultiplication. -/
@[simp, stacks 0G5N "canonical comonad resolution degeneracy formula"]
theorem simplicialResolution.degeneracy {n : ℕ} (i : Fin (n + 1)) :
    G.simplicialResolution.σ i =
      IteratedEndofunctor.degeneracy G.δ n i := by
  set_option backward.isDefEq.respectTransparency false in
    change EndofunctorResolution.simplicial.map G.ε G.δ (SimplexCategory.σ i).op =
      IteratedEndofunctor.degeneracy G.δ n i
    have h := (EndofunctorResolution.simplicial.resolution.realization G.ε G.δ
      (simplicialResolution.right_counit G) (simplicialResolution.left_counit G)
      (simplicialResolution.coassoc G)).σ_eq i
    change 𝟙 _ ≫ IteratedEndofunctor.degeneracy G.δ n i =
      EndofunctorResolution.simplicial.map G.ε G.δ (SimplexCategory.σ i).op ≫ 𝟙 _ at h
    simpa only [Category.id_comp, Category.comp_id] using h.symm

/-- The raw degreewise component induced between the canonical resolutions of two comonads. -/
@[stacks 0G5N "component of the comonad resolution map"]
noncomputable def simplicialResolution.homApp {G H : Comonad C} (α : G ⟶ H)
    (Δ : SimplexCategoryᵒᵖ) :
    G.toFunctor ⁺⦋Δ.unop.len⦌ ⟶ H.toFunctor ⁺⦋Δ.unop.len⦌ :=
  Endofunctor.iterate.map α.toNatTrans (Δ.unop.len + 1)

set_option backward.isDefEq.respectTransparency false in
private theorem resolution_face_naturality {G H : Comonad C} (α : G ⟶ H)
    (n : ℕ) (i : Fin (n + 2)) :
    IteratedEndofunctor.face G.ε n i ≫ Endofunctor.iterate.map α.toNatTrans (n + 1) =
      Endofunctor.iterate.map α.toNatTrans (n + 2) ≫ IteratedEndofunctor.face H.ε n i := by
  induction n with
  | zero =>
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp only [IteratedEndofunctor.face, Fin.lastCases_last]
        ext X
        change (G.ε.app (G.obj X) ≫ 𝟙 _) ≫ (α.app X ≫ H.map (𝟙 X)) =
          (α.app (G.obj X) ≫ H.map (α.app X ≫ H.map (𝟙 X))) ≫
            (H.ε.app (H.obj X) ≫ 𝟙 _)
        simp only [H.map_id, Category.comp_id]
        rw [Category.assoc, H.counit_naturality, ← Category.assoc, α.app_ε]
      · simp only [IteratedEndofunctor.face, Fin.lastCases_castSucc]
        ext X
        change (G.map (G.ε.app X) ≫ 𝟙 _) ≫ (α.app X ≫ H.map (𝟙 X)) =
          (α.app (G.obj X) ≫ H.map (α.app X ≫ H.map (𝟙 X))) ≫
            (H.map (H.ε.app X) ≫ 𝟙 _)
        simp only [H.map_id, Category.comp_id]
        rw [Category.assoc, ← H.map_comp, α.app_ε]
        simpa only [Functor.id_obj] using α.toNatTrans.naturality (G.ε.app X)
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp only [IteratedEndofunctor.face, Fin.lastCases_last]
        ext X
        change (G.ε.app ((Endofunctor.iterate G.toFunctor (n + 2)).obj X) ≫ 𝟙 _) ≫
            (Endofunctor.iterate.map α.toNatTrans (n + 2)).app X =
          (α.app ((Endofunctor.iterate G.toFunctor (n + 2)).obj X) ≫
            H.map ((Endofunctor.iterate.map α.toNatTrans (n + 2)).app X)) ≫
              (H.ε.app ((Endofunctor.iterate H.toFunctor (n + 2)).obj X) ≫ 𝟙 _)
        simp only [Category.comp_id]
        rw [Category.assoc, H.counit_naturality, ← Category.assoc, α.app_ε]
      · simp only [IteratedEndofunctor.face, Fin.lastCases_castSucc]
        ext X
        change G.map ((IteratedEndofunctor.face G.ε n j).app X) ≫
            (α.app ((Endofunctor.iterate G.toFunctor (n + 1)).obj X) ≫
              H.map ((Endofunctor.iterate.map α.toNatTrans (n + 1)).app X)) =
          (α.app ((Endofunctor.iterate G.toFunctor (n + 2)).obj X) ≫
            H.map ((Endofunctor.iterate.map α.toNatTrans (n + 2)).app X)) ≫
              H.map ((IteratedEndofunctor.face H.ε n j).app X)
        rw [← Category.assoc]
        erw [α.toNatTrans.naturality]
        rw [Category.assoc, ← H.map_comp]
        have h := NatTrans.congr_app (ih j) X
        dsimp only [NatTrans.comp_app] at h
        erw [h, H.map_comp, Category.assoc]
        rfl

set_option backward.isDefEq.respectTransparency false in
private theorem resolution_degeneracy_naturality {G H : Comonad C} (α : G ⟶ H)
    (n : ℕ) (i : Fin (n + 1)) :
    IteratedEndofunctor.degeneracy G.δ n i ≫
        Endofunctor.iterate.map α.toNatTrans (n + 2) =
      Endofunctor.iterate.map α.toNatTrans (n + 1) ≫
        IteratedEndofunctor.degeneracy H.δ n i := by
  induction n with
  | zero =>
      ext X
      change G.δ.app X ≫
          (α.app (G.obj X) ≫ H.map (α.app X ≫ H.map (𝟙 X))) =
        (α.app X ≫ H.map (𝟙 X)) ≫ H.δ.app X
      simpa only [H.map_id, Category.comp_id] using (α.app_δ X).symm
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp only [IteratedEndofunctor.degeneracy, Fin.lastCases_last]
        ext X
        change (G.δ.app ((Endofunctor.iterate G.toFunctor (n + 1)).obj X) ≫ 𝟙 _) ≫
            (α.app (G.obj ((Endofunctor.iterate G.toFunctor (n + 1)).obj X)) ≫
              H.map (α.app ((Endofunctor.iterate G.toFunctor (n + 1)).obj X) ≫
                H.map ((Endofunctor.iterate.map α.toNatTrans (n + 1)).app X))) =
          (α.app ((Endofunctor.iterate G.toFunctor (n + 1)).obj X) ≫
            H.map ((Endofunctor.iterate.map α.toNatTrans (n + 1)).app X)) ≫
              (H.δ.app ((Endofunctor.iterate H.toFunctor (n + 1)).obj X) ≫ 𝟙 _)
        simp only [Category.comp_id, H.map_comp, Category.assoc]
        rw [← α.app_δ_assoc, ← H.delta_naturality, ← Category.assoc]
      · simp only [IteratedEndofunctor.degeneracy, Fin.lastCases_castSucc]
        ext X
        change G.map ((IteratedEndofunctor.degeneracy G.δ n j).app X) ≫
            (α.app ((Endofunctor.iterate G.toFunctor (n + 2)).obj X) ≫
              H.map ((Endofunctor.iterate.map α.toNatTrans (n + 2)).app X)) =
          (α.app ((Endofunctor.iterate G.toFunctor (n + 1)).obj X) ≫
            H.map ((Endofunctor.iterate.map α.toNatTrans (n + 1)).app X)) ≫
              H.map ((IteratedEndofunctor.degeneracy H.δ n j).app X)
        rw [← Category.assoc]
        erw [α.toNatTrans.naturality]
        rw [Category.assoc, ← H.map_comp]
        have h := NatTrans.congr_app (ih j) X
        dsimp only [NatTrans.comp_app] at h
        erw [h, H.map_comp, Category.assoc]
        rfl

set_option backward.isDefEq.respectTransparency false in
private theorem resolution_evalCode_naturality {G H : Comonad C} (α : G ⟶ H)
    {m n : ℕ} (code : SimplexCategory.HomCode m n) :
    EndofunctorResolution.simplicial.evalCode G.ε G.δ code ≫
        Endofunctor.iterate.map α.toNatTrans (m + 1) =
      Endofunctor.iterate.map α.toNatTrans (n + 1) ≫
        EndofunctorResolution.simplicial.evalCode H.ε H.δ code := by
  induction code with
  | id n =>
      dsimp only [EndofunctorResolution.simplicial.evalCode]
      change (𝟙 _ ≫ Endofunctor.iterate.map α.toNatTrans (n + 1)) =
        Endofunctor.iterate.map α.toNatTrans (n + 1) ≫
          𝟙 (Endofunctor.iterate H.toFunctor (n + 1))
      simp only [Category.id_comp, Category.comp_id]
  | face i code ih =>
      dsimp only [EndofunctorResolution.simplicial.evalCode]
      rw [Category.assoc, ih, ← Category.assoc, resolution_face_naturality, Category.assoc]
  | degeneracy i code ih =>
      dsimp only [EndofunctorResolution.simplicial.evalCode]
      rw [Category.assoc, resolution_degeneracy_naturality, ← Category.assoc, ih, Category.assoc]

/-- The raw components `simplicialResolution.homApp α` form a natural family. -/
@[stacks 0G5N "naturality of the comonad resolution map"]
theorem simplicialResolution.homApp.naturality {G H : Comonad C} (α : G ⟶ H)
    {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') :
    G.simplicialResolution.map θ ≫
        simplicialResolution.homApp α Δ' =
      simplicialResolution.homApp α Δ ≫
        H.simplicialResolution.map θ := by
  change EndofunctorResolution.simplicial.map G.ε G.δ θ ≫
      Endofunctor.iterate.map α.toNatTrans (Δ'.unop.len + 1) =
    Endofunctor.iterate.map α.toNatTrans (Δ.unop.len + 1) ≫
      EndofunctorResolution.simplicial.map H.ε H.δ θ
  exact resolution_evalCode_naturality α
    (SimplexCategory.HomCode.ofHom Δ'.unop.len Δ.unop.len (SimplexCategory.canonicalHom θ))

/-- The simplicial resolution map induced by a morphism of comonads. -/
@[stacks 0G5N "map of comonad resolutions"]
noncomputable def simplicialResolution.hom {G H : Comonad C} (α : G ⟶ H) :
    G.simplicialResolution ⟶ H.simplicialResolution where
  app := simplicialResolution.homApp α
  naturality := fun _ _ θ ↦ simplicialResolution.homApp.naturality α θ

/-- A comonad-resolution map is degreewise the iterated underlying natural transformation. -/
@[simp, stacks 0G5N "component formula for the comonad resolution map"]
theorem simplicialResolution.hom_app {G H : Comonad C} (α : G ⟶ H)
    (Δ : SimplexCategoryᵒᵖ) :
    (simplicialResolution.hom α).app Δ =
      simplicialResolution.homApp α Δ := by
  rfl

/-- The resolution map induced by the identity comonad morphism is the identity. -/
@[simp, stacks 0G5N "identity map of comonad resolutions"]
theorem simplicialResolution.hom.id (G : Comonad C) :
    simplicialResolution.hom (𝟙 G) = 𝟙 (G.simplicialResolution) := by
  apply NatTrans.ext
  funext Δ
  change Endofunctor.iterate.map (𝟙 G : G ⟶ G).toNatTrans (Δ.unop.len + 1) = 𝟙 _
  rw [ComonadHom.id_toNatTrans, Endofunctor.iterate.map.id]

/-- Resolution maps preserve composition of comonad morphisms. -/
@[simp, stacks 0G5N "composition of comonad resolution maps"]
theorem simplicialResolution.hom.comp {G H K : Comonad C}
    (α : G ⟶ H) (β : H ⟶ K) :
    simplicialResolution.hom (α ≫ β) =
      simplicialResolution.hom α ≫ simplicialResolution.hom β := by
  apply NatTrans.ext
  funext Δ
  change Endofunctor.iterate.map (α ≫ β).toNatTrans (Δ.unop.len + 1) =
    Endofunctor.iterate.map α.toNatTrans (Δ.unop.len + 1) ≫
      Endofunctor.iterate.map β.toNatTrans (Δ.unop.len + 1)
  exact Endofunctor.iterate.map.comp α.toNatTrans β.toNatTrans (Δ.unop.len + 1)

/-- The canonical simplicial resolution as a functor of the comonad. -/
@[stacks 0G5N "functorial comonad resolution"]
noncomputable def simplicialResolution.functor :
    Comonad C ⥤ SimplicialObject (C ⥤ C) where
  obj G := G.simplicialResolution
  map α := simplicialResolution.hom α
  map_id := simplicialResolution.hom.id
  map_comp := simplicialResolution.hom.comp

/-- The canonical comonad resolution realizes the positive iterates, counit faces, and
comultiplication degeneracies. -/
@[stacks 0G5N "canonical comonad resolution realization"]
theorem simplicialResolution.realization :
    G.Realizes G.simplicialResolution := by
  exact EndofunctorResolution.simplicial.resolution.realization G.ε G.δ
    (simplicialResolution.right_counit G) (simplicialResolution.left_counit G)
    (simplicialResolution.coassoc G)

variable {G : Comonad C}

/-- Every realization of a comonad's iterated formulas is the canonical simplicial
resolution. -/
@[stacks 0G5N "identification with the canonical comonad resolution"]
theorem Realizes.eq_simplicialResolution {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U) : U = G.simplicialResolution := by
  exact EndofunctorResolution.Realization.eq_resolution G.ε G.δ
    (simplicialResolution.right_counit G) (simplicialResolution.left_counit G)
    (simplicialResolution.coassoc G) hU

/-- The degree isomorphisms of a realization are natural with respect to the canonical
comonad resolution. -/
@[stacks 0G5N "naturality of the canonical realization isomorphism"]
theorem Realizes.iso_hom_naturality {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U) {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') :
    U.map θ ≫ (hU.objIso Δ'.unop.len).hom =
      (hU.objIso Δ.unop.len).hom ≫ G.simplicialResolution.map θ := by
  exact (EndofunctorResolution.Realization.map.eq hU θ).symm

/-- A realization is canonically isomorphic to the comonad's simplicial resolution. Its
components are the explicit degree isomorphisms stored by the realization witness. -/
@[stacks 0G5N "canonical isomorphism from a realization to the comonad resolution"]
noncomputable def Realizes.iso {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U) : U ≅ G.simplicialResolution :=
  NatIso.ofComponents (fun Δ ↦ hU.objIso Δ.unop.len)
    (fun θ ↦ Realizes.iso_hom_naturality hU θ)

/-- The forward component of the canonical realization isomorphism is the realization's
explicit degree transport. -/
@[simp, stacks 0G5N "forward component of the canonical realization isomorphism"]
theorem Realizes.iso_hom_app {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U) (Δ : SimplexCategoryᵒᵖ) :
    (Realizes.iso hU).hom.app Δ = (hU.objIso Δ.unop.len).hom := by
  rfl

/-- The inverse component of the canonical realization isomorphism is the reverse degree
transport supplied by the realization witness. -/
@[simp, stacks 0G5N "inverse component of the canonical realization isomorphism"]
theorem Realizes.iso_inv_app {U : SimplicialObject (C ⥤ C)}
    (hU : G.Realizes U) (Δ : SimplexCategoryᵒᵖ) :
    (Realizes.iso hU).inv.app Δ = (hU.objIso Δ.unop.len).inv := by
  rfl

variable (G : Comonad C)

/-- The canonical simplicial resolution is the unique realization of a comonad's iterated
endofunctor formulas. -/
@[stacks 0G5N "uniqueness of the canonical comonad resolution"]
theorem Realizes.existsUnique :
    ∃! U : SimplicialObject (C ⥤ C), G.Realizes U := by
  exact ⟨G.simplicialResolution, simplicialResolution.realization G,
    fun U hU ↦ Realizes.eq_simplicialResolution hU⟩

end Comonad

namespace EndofunctorResolution.toComonad

/-- The canonical simplicial resolution of the comonad generated by raw counit and
comultiplication data is the raw iterated-endofunctor resolution. -/
@[stacks 0G5N "raw resolution agrees with the generated comonad resolution"]
theorem simplicialResolution_eq {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (hσδ₀ : IteratedEndofunctor.degeneracy s 0 0 ≫
      IteratedEndofunctor.face d 0 0 = 𝟙 Y)
    (hσδ₁ : IteratedEndofunctor.degeneracy s 0 0 ≫
      IteratedEndofunctor.face d 0 1 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.degeneracy s 0 0 ≫
        IteratedEndofunctor.degeneracy s 1 0 =
      IteratedEndofunctor.degeneracy s 0 0 ≫
        IteratedEndofunctor.degeneracy s 1 1) :
    (EndofunctorResolution.toComonad d s hσδ₀ hσδ₁ hσσ).simplicialResolution =
      EndofunctorResolution.simplicial.resolution d s hσδ₀ hσδ₁ hσσ := by
  rfl

end EndofunctorResolution.toComonad

end CategoryTheory
