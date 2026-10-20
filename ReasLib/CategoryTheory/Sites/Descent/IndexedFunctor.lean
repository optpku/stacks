/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor
public import ReasLib.CategoryTheory.Sites.Descent.Basic
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf
public import ReasLib.CategoryTheory.Sites.Over

/-!
# Descent along an indexed functor

The `pullHom` construction is natural with respect to a universe-polymorphic
`LocallyDiscreteOpToCat.IndexedFunctor`.  This is the reusable coherence statement needed when
descent data are transported between indexed categories over different bases.

For a fiberwise-fully-faithful indexed functor, the same API identifies Hom presheaves after
pullback along `Over.post`, including the universe lift forced by different fiber hom universes.
The final prestack transfer theorems keep continuity and sheaf transport out of application
proofs.  Essential surjectivity of the fiber components is not needed at this layer.
-/

@[expose] public section

universe uC vC uD vD uF vF uG vG w

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {u : C ⥤ D}
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vG, uG}}

/-- Transport by an indexed functor commutes with `pullHom` when both mapped composite
equalities are supplied explicitly. -/
theorem mapHom_pullHom_of_mapped_eq (H : IndexedFunctor u F G)
    {U₁ U₂ V W : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    (g : W ⟶ V) (gf₁ : W ⟶ U₁) (gf₂ : W ⟶ U₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (hugf₁ : u.map g ≫ u.map f₁ = u.map gf₁)
    (hugf₂ : u.map g ≫ u.map f₂ = u.map gf₂)
    {x : F.obj (LocallyDiscrete.mk (Opposite.op U₁))}
    {y : F.obj (LocallyDiscrete.mk (Opposite.op U₂))}
    (φ :
      (F.map f₁.op.toLoc).toFunctor.obj x ⟶
        (F.map f₂.op.toLoc).toFunctor.obj y) :
    H.mapHom gf₁ gf₂
        (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) =
      pullHom
        (H.mapHom f₁ f₂ φ) (u.map g) (u.map gf₁) (u.map gf₂)
          hugf₁ hugf₂ := sorry

/-- Transport by an indexed functor commutes with `pullHom`.  Mapped composite equalities are
discharged from the two source equalities by the category tactic, so callers only supply the
geometric factorization data they already have. -/
theorem mapHom_pullHom (H : IndexedFunctor u F G)
    {U₁ U₂ V W : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    (g : W ⟶ V) (gf₁ : W ⟶ U₁) (gf₂ : W ⟶ U₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    {x : F.obj (LocallyDiscrete.mk (Opposite.op U₁))}
    {y : F.obj (LocallyDiscrete.mk (Opposite.op U₂))}
    (φ :
      (F.map f₁.op.toLoc).toFunctor.obj x ⟶
        (F.map f₂.op.toLoc).toFunctor.obj y) :
    H.mapHom gf₁ gf₂
        (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) =
      pullHom
        (H.mapHom f₁ f₂ φ) (u.map g) (u.map gf₁) (u.map gf₂) := sorry

/-- Literal-composite form of `mapHom_pullHom`; it requires no equality arguments. -/
theorem mapHom_pullHom_comp (H : IndexedFunctor u F G)
    {U₁ U₂ V W : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂) (g : W ⟶ V)
    {x : F.obj (LocallyDiscrete.mk (Opposite.op U₁))}
    {y : F.obj (LocallyDiscrete.mk (Opposite.op U₂))}
    (φ :
      (F.map f₁.op.toLoc).toFunctor.obj x ⟶
        (F.map f₂.op.toLoc).toFunctor.obj y) :
    H.mapHom (g ≫ f₁) (g ≫ f₂)
        (pullHom φ g (g ≫ f₁) (g ≫ f₂)) =
      pullHom
        (H.mapHom f₁ f₂ φ) (u.map g)
          (u.map (g ≫ f₁)) (u.map (g ≫ f₂)) := sorry

/-- Inverse restricted-hom transport commutes with `pullHom` when both mapped composite
equalities are supplied explicitly.  This is the inverse orientation of
`mapHom_pullHom_of_mapped_eq`. -/
theorem mapHomEquiv_symm_apply_pullHom_of_mapped_eq
    (H : IndexedFunctor u F G) [H.FiberwiseFullyFaithful]
    {U₁ U₂ V W : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    (g : W ⟶ V) (gf₁ : W ⟶ U₁) (gf₂ : W ⟶ U₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (hugf₁ : u.map g ≫ u.map f₁ = u.map gf₁)
    (hugf₂ : u.map g ≫ u.map f₂ = u.map gf₂)
    {x : F.obj (LocallyDiscrete.mk (Opposite.op U₁))}
    {y : F.obj (LocallyDiscrete.mk (Opposite.op U₂))}
    (ψ :
      (G.map (u.map f₁).op.toLoc).toFunctor.obj ((H.app U₁).obj x) ⟶
        (G.map (u.map f₂).op.toLoc).toFunctor.obj ((H.app U₂).obj y)) :
    (H.mapHomEquiv gf₁ gf₂).symm
        (pullHom ψ (u.map g) (u.map gf₁) (u.map gf₂)
          hugf₁ hugf₂) =
      pullHom ((H.mapHomEquiv f₁ f₂).symm ψ)
        g gf₁ gf₂ hgf₁ hgf₂ := sorry

/-- Inverse restricted-hom transport commutes with `pullHom`.  The mapped composite equalities
are derived from the source factorization equalities. -/
theorem mapHomEquiv_symm_apply_pullHom
    (H : IndexedFunctor u F G) [H.FiberwiseFullyFaithful]
    {U₁ U₂ V W : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    (g : W ⟶ V) (gf₁ : W ⟶ U₁) (gf₂ : W ⟶ U₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    {x : F.obj (LocallyDiscrete.mk (Opposite.op U₁))}
    {y : F.obj (LocallyDiscrete.mk (Opposite.op U₂))}
    (ψ :
      (G.map (u.map f₁).op.toLoc).toFunctor.obj ((H.app U₁).obj x) ⟶
        (G.map (u.map f₂).op.toLoc).toFunctor.obj ((H.app U₂).obj y)) :
    (H.mapHomEquiv gf₁ gf₂).symm
        (pullHom ψ (u.map g) (u.map gf₁) (u.map gf₂)) =
      pullHom ((H.mapHomEquiv f₁ f₂).symm ψ)
        g gf₁ gf₂ hgf₁ hgf₂ := sorry

/-- Literal-composite form of compatibility between inverse restricted-hom transport and
`pullHom`; it requires no equality arguments. -/
theorem mapHomEquiv_symm_apply_pullHom_comp
    (H : IndexedFunctor u F G) [H.FiberwiseFullyFaithful]
    {U₁ U₂ V W : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂) (g : W ⟶ V)
    {x : F.obj (LocallyDiscrete.mk (Opposite.op U₁))}
    {y : F.obj (LocallyDiscrete.mk (Opposite.op U₂))}
    (ψ :
      (G.map (u.map f₁).op.toLoc).toFunctor.obj ((H.app U₁).obj x) ⟶
        (G.map (u.map f₂).op.toLoc).toFunctor.obj ((H.app U₂).obj y)) :
    (H.mapHomEquiv (g ≫ f₁) (g ≫ f₂)).symm
        (pullHom ψ (u.map g)
          (u.map (g ≫ f₁)) (u.map (g ≫ f₂))) =
      pullHom ((H.mapHomEquiv f₁ f₂).symm ψ)
        g (g ≫ f₁) (g ≫ f₂) := sorry

namespace HomPresheaf

variable {F₀ : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max w vG, uF}}
variable {G₀ : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vG, uG}}

/-- Objectwise equivalence between a source Hom presheaf and the corresponding target Hom
presheaf pulled back along the base functor.  The target hom-set is lifted by `w` to match the
source hom universe. -/
noncomputable def appEquiv
    (H : IndexedFunctor u F₀ G₀) [H.FiberwiseFullyFaithful]
    {U : C} (x y : F₀.obj (LocallyDiscrete.mk (Opposite.op U)))
    (T : Over U) :
    (F₀.presheafHom x y).obj (Opposite.op T) ≃
      (((Over.post u).op ⋙
        G₀.presheafHom ((H.app U).obj x) ((H.app U).obj y) ⋙
          uliftFunctor.{w}).obj (Opposite.op T)) :=
  (H.mapHomEquiv T.hom T.hom).trans Equiv.ulift.symm

/-- The forward objectwise Hom-presheaf equivalence is `mapHom` followed by `ULift.up`. -/
@[simp]
theorem appEquiv_apply
    (H : IndexedFunctor u F₀ G₀) [H.FiberwiseFullyFaithful]
    {U : C} (x y : F₀.obj (LocallyDiscrete.mk (Opposite.op U)))
    (T : Over U) (φ : (F₀.presheafHom x y).obj (Opposite.op T)) :
    appEquiv H x y T φ =
      ULift.up (H.mapHom T.hom T.hom φ) := sorry

/-- The inverse objectwise Hom-presheaf equivalence removes the universe lift and applies
inverse restricted-morphism transport. -/
@[simp]
theorem appEquiv_symm_apply
    (H : IndexedFunctor u F₀ G₀) [H.FiberwiseFullyFaithful]
    {U : C} (x y : F₀.obj (LocallyDiscrete.mk (Opposite.op U)))
    (T : Over U)
    (ψ : (((Over.post u).op ⋙
      G₀.presheafHom ((H.app U).obj x) ((H.app U).obj y) ⋙
        uliftFunctor.{w}).obj (Opposite.op T))) :
    (appEquiv H x y T).symm ψ =
      (H.mapHomEquiv T.hom T.hom).symm ψ.down := sorry

/-- Elementwise naturality of the Hom-presheaf equivalence in `pullHom` normal form.  Removing
the universe lift after restricting a section is the same as restricting its transported
section. -/
theorem appEquiv_pullHom_down
    (H : IndexedFunctor u F₀ G₀) [H.FiberwiseFullyFaithful]
    {U : C} (x y : F₀.obj (LocallyDiscrete.mk (Opposite.op U)))
    {T₁ T₂ : Over U} (g : T₂ ⟶ T₁)
    (φ : (F₀.presheafHom x y).obj (Opposite.op T₁)) :
    ((appEquiv H x y T₂)
        (pullHom φ g.left T₂.hom T₂.hom)).down =
      pullHom (H.mapHom T₁.hom T₁.hom φ)
        (u.map g.left) (u.map T₂.hom) (u.map T₂.hom)
          (Over.post_map_left_comp_hom u g)
          (Over.post_map_left_comp_hom u g) := sorry

/-- The objectwise Hom-presheaf equivalences induced by a fiberwise-fully-faithful indexed
functor are natural in the slice object. -/
theorem appEquiv_naturality
    (H : IndexedFunctor u F₀ G₀) [H.FiberwiseFullyFaithful]
    {U : C} (x y : F₀.obj (LocallyDiscrete.mk (Opposite.op U))) :
    ∀ {T₁ T₂ : (Over U)ᵒᵖ} (α : T₁ ⟶ T₂),
      (F₀.presheafHom x y).map α ≫
          (Equiv.toIso (appEquiv H x y T₂.unop)).hom =
        (Equiv.toIso (appEquiv H x y T₁.unop)).hom ≫
          (((Over.post u).op ⋙
            G₀.presheafHom ((H.app U).obj x) ((H.app U).obj y) ⋙
              uliftFunctor.{w}).map α) := sorry

/-- A fiberwise-fully-faithful indexed functor identifies source Hom presheaves with target Hom
presheaves pulled back along its base functor, after the necessary universe lift. -/
noncomputable def iso
    (H : IndexedFunctor u F₀ G₀) [H.FiberwiseFullyFaithful]
    {U : C} (x y : F₀.obj (LocallyDiscrete.mk (Opposite.op U))) :
    F₀.presheafHom x y ≅
      (Over.post u).op ⋙
        G₀.presheafHom ((H.app U).obj x) ((H.app U).obj y) ⋙
          uliftFunctor.{w} :=
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso (appEquiv H x y T.unop))
    (appEquiv_naturality H x y)

namespace Iso

/-- Forward components of the Hom-presheaf isomorphism are the objectwise Hom equivalences. -/
@[simp]
theorem hom_app
    (H : IndexedFunctor u F₀ G₀) [H.FiberwiseFullyFaithful]
    {U : C} (x y : F₀.obj (LocallyDiscrete.mk (Opposite.op U)))
    (T : (Over U)ᵒᵖ) :
    (HomPresheaf.iso H x y).hom.app T =
      (Equiv.toIso (HomPresheaf.appEquiv H x y T.unop)).hom := sorry

/-- Inverse components of the Hom-presheaf isomorphism are the inverse objectwise Hom
equivalences. -/
@[simp]
theorem inv_app
    (H : IndexedFunctor u F₀ G₀) [H.FiberwiseFullyFaithful]
    {U : C} (x y : F₀.obj (LocallyDiscrete.mk (Opposite.op U)))
    (T : (Over U)ᵒᵖ) :
    (HomPresheaf.iso H x y).inv.app T =
      (Equiv.toIso (HomPresheaf.appEquiv H x y T.unop)).inv := sorry

end Iso

/-- Sheafness of a source Hom presheaf is equivalent to sheafness of the corresponding
unlifted target Hom presheaf pulled back along `Over.post`.  This packages both transport across
`HomPresheaf.iso` and invariance under `uliftFunctor`. -/
theorem isSheaf_iff
    (H : IndexedFunctor u F₀ G₀) [H.FiberwiseFullyFaithful]
    (J : GrothendieckTopology C)
    {U : C} (x y : F₀.obj (LocallyDiscrete.mk (Opposite.op U))) :
    Presheaf.IsSheaf (J.over U) (F₀.presheafHom x y) ↔
      Presheaf.IsSheaf (J.over U)
        ((Over.post u).op ⋙
          G₀.presheafHom ((H.app U).obj x) ((H.app U).obj y)) := sorry

namespace IsPrestack

/-- A fiberwise-fully-faithful indexed functor transfers the prestack condition from sheafness
of the pulled-back target Hom presheaves.  Callers supply only the geometric sheaf-transport
fact; the Hom equivalence, universe lift, and sheaf transport across the resulting isomorphism
are encapsulated here. -/
theorem of_isSheaf_comp
    (H : IndexedFunctor u F₀ G₀) [H.FiberwiseFullyFaithful]
    (J : GrothendieckTopology C)
    (h : ∀ (U : C)
      (x y : F₀.obj (LocallyDiscrete.mk (Opposite.op U))),
      Presheaf.IsSheaf (J.over U)
        ((Over.post u).op ⋙
          G₀.presheafHom ((H.app U).obj x) ((H.app U).obj y))) :
    Pseudofunctor.IsPrestack F₀ J := sorry

/-- A fiberwise-fully-faithful indexed functor transfers the prestack condition along a base
functor whose induced functor on every slice is continuous. -/
theorem of_isPrestack
    (H : IndexedFunctor u F₀ G₀) [H.FiberwiseFullyFaithful]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Pseudofunctor.IsPrestack G₀ K]
    (h_continuous : ∀ U : C,
      (Over.post u).IsContinuous (J.over U) (K.over (u.obj U))) :
    Pseudofunctor.IsPrestack F₀ J := sorry

/-- A fiberwise-fully-faithful indexed functor transfers the prestack condition along a
continuous base functor.  Slice continuity is supplied by
`Functor.IsContinuous.overPost`, so applications need no per-object continuity argument. -/
theorem of_isContinuous
    (H : IndexedFunctor u F₀ G₀) [H.FiberwiseFullyFaithful]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Pseudofunctor.IsPrestack G₀ K] [u.IsContinuous J K] :
    Pseudofunctor.IsPrestack F₀ J := sorry

end IsPrestack

end HomPresheaf

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
