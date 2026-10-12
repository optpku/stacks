/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.IndexedFunctor
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor

/-!
# Descent through categorical-pullback fiber comparisons

These application-facing theorems specialize the generic `IndexedFunctor.mapHom_pullHom` API to
the fiber comparison for a categorical pullback.  They replace manual expansions of `pullHom`,
cartesian factorization, and change-of-cleavage conjugation.

The Hom-presheaf and prestack declarations are thin specializations of the generic indexed
equivalence API.  Their source is exactly mathlib's selected
`fiberPseudofunctor (π₁ u p)`.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

universe uC uD uS vC vD vS

namespace CategoryTheory

open Functor Opposite
open scoped CategoryTheory.Bicategory

namespace Limits.CategoricalPullback

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- The explicit-cleavage pullback-fiber comparison commutes with `pullHom`. -/
theorem Indexed.explicit.functor.mapHom.pullHom
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U₁ U₂ V W : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    (g : W ⟶ V) (gf₁ : W ⟶ U₁) (gf₂ : W ⟶ U₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    {X : (π₁ u p).Fiber U₁} {Y : (π₁ u p).Fiber U₂}
    (φ :
      (((χ.ofRight u).toPseudofunctor.map
        f₁.op.toLoc).toFunctor.obj X) ⟶
      (((χ.ofRight u).toPseudofunctor.map
        f₂.op.toLoc).toFunctor.obj Y)) :
    (Indexed.explicit.functor u p χ).mapHom gf₁ gf₂
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          φ g gf₁ gf₂ hgf₁ hgf₂) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        ((Indexed.explicit.functor u p χ).mapHom f₁ f₂ φ)
        (u.map g) (u.map gf₁) (u.map gf₂) := sorry

/-- Literal-composite form of compatibility between the explicit pullback-fiber comparison and
`pullHom`. -/
theorem Indexed.explicit.functor.mapHom.pullHom.comp
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U₁ U₂ V W : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂) (g : W ⟶ V)
    {X : (π₁ u p).Fiber U₁} {Y : (π₁ u p).Fiber U₂}
    (φ :
      (((χ.ofRight u).toPseudofunctor.map
        f₁.op.toLoc).toFunctor.obj X) ⟶
      (((χ.ofRight u).toPseudofunctor.map
        f₂.op.toLoc).toFunctor.obj Y)) :
    (Indexed.explicit.functor u p χ).mapHom
        (g ≫ f₁) (g ≫ f₂)
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          φ g (g ≫ f₁) (g ≫ f₂)) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        ((Indexed.explicit.functor u p χ).mapHom f₁ f₂ φ)
        (u.map g) (u.map (g ≫ f₁)) (u.map (g ≫ f₂)) := sorry

/-- The canonical selected-cleavage pullback-fiber comparison commutes with `pullHom`.

Its source is exactly `fiberPseudofunctor (π₁ u p)`, so applications do not need to change their
existing pseudofunctor presentation before using this theorem. -/
theorem Indexed.canonical.functor.mapHom.pullHom
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U₁ U₂ V W : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    (g : W ⟶ V) (gf₁ : W ⟶ U₁) (gf₂ : W ⟶ U₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    {X : (π₁ u p).Fiber U₁} {Y : (π₁ u p).Fiber U₂}
    (φ :
      ((fiberPseudofunctor (π₁ u p)).map f₁.op.toLoc).toFunctor.obj X ⟶
        ((fiberPseudofunctor (π₁ u p)).map f₂.op.toLoc).toFunctor.obj Y) :
    (Indexed.canonical.functor u p).mapHom gf₁ gf₂
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          φ g gf₁ gf₂ hgf₁ hgf₂) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        ((Indexed.canonical.functor u p).mapHom f₁ f₂ φ)
        (u.map g) (u.map gf₁) (u.map gf₂) := sorry

/-- Literal-composite form of compatibility between the canonical selected-cleavage
pullback-fiber comparison and `pullHom`; no equality arguments are required. -/
theorem Indexed.canonical.functor.mapHom.pullHom.comp
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U₁ U₂ V W : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂) (g : W ⟶ V)
    {X : (π₁ u p).Fiber U₁} {Y : (π₁ u p).Fiber U₂}
    (φ :
      ((fiberPseudofunctor (π₁ u p)).map f₁.op.toLoc).toFunctor.obj X ⟶
        ((fiberPseudofunctor (π₁ u p)).map f₂.op.toLoc).toFunctor.obj Y) :
    (Indexed.canonical.functor u p).mapHom
        (g ≫ f₁) (g ≫ f₂)
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          φ g (g ≫ f₁) (g ≫ f₂)) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        ((Indexed.canonical.functor u p).mapHom f₁ f₂ φ)
        (u.map g) (u.map (g ≫ f₁)) (u.map (g ≫ f₂)) := sorry

/-- Inverse canonical restricted-hom transport commutes with `pullHom`. -/
theorem Indexed.canonical.homEquiv.symm.pullHom
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U₁ U₂ V W : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    (g : W ⟶ V) (gf₁ : W ⟶ U₁) (gf₂ : W ⟶ U₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    {X : (π₁ u p).Fiber U₁} {Y : (π₁ u p).Fiber U₂}
    (ψ :
      ((fiberPseudofunctor p).map
          (u.map f₁).op.toLoc).toFunctor.obj
            ((Fiber.chosen.functor u p U₁).obj X) ⟶
        ((fiberPseudofunctor p).map
          (u.map f₂).op.toLoc).toFunctor.obj
            ((Fiber.chosen.functor u p U₂).obj Y)) :
    (Indexed.canonical.homEquiv u p gf₁ gf₂).symm
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          ψ (u.map g) (u.map gf₁) (u.map gf₂)) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        ((Indexed.canonical.homEquiv
          u p f₁ f₂).symm ψ)
        g gf₁ gf₂ hgf₁ hgf₂ := sorry

/-- Literal-composite form of compatibility between inverse canonical restricted-hom
transport and `pullHom`. -/
theorem Indexed.canonical.homEquiv.symm.pullHom.comp
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U₁ U₂ V W : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂) (g : W ⟶ V)
    {X : (π₁ u p).Fiber U₁} {Y : (π₁ u p).Fiber U₂}
    (ψ :
      ((fiberPseudofunctor p).map
          (u.map f₁).op.toLoc).toFunctor.obj
            ((Fiber.chosen.functor u p U₁).obj X) ⟶
        ((fiberPseudofunctor p).map
          (u.map f₂).op.toLoc).toFunctor.obj
            ((Fiber.chosen.functor u p U₂).obj Y)) :
    (Indexed.canonical.homEquiv
        u p (g ≫ f₁) (g ≫ f₂)).symm
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            ψ (u.map g) (u.map (g ≫ f₁)) (u.map (g ≫ f₂))) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        ((Indexed.canonical.homEquiv
          u p f₁ f₂).symm ψ)
        g (g ≫ f₁) (g ≫ f₂) := sorry

/-- Objectwise hom-set equivalence underlying the Hom-presheaf comparison for a categorical
pullback.  The target is lifted only by the base hom universe, which is exactly the resizing
needed to match morphisms in the categorical pullback. -/
noncomputable def Indexed.canonical.homPresheaf.appEquiv
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U : C} (X Y : (π₁ u p).Fiber U) (T : Over U) :
    ((fiberPseudofunctor (π₁ u p)).presheafHom X Y).obj
        (Opposite.op T) ≃
      (((Over.post u).op ⋙
        (fiberPseudofunctor p).presheafHom
          ((Fiber.chosen.functor u p U).obj X)
          ((Fiber.chosen.functor u p U).obj Y) ⋙
            uliftFunctor.{vC}).obj (Opposite.op T)) :=
  Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.HomPresheaf.appEquiv
    (Indexed.canonical.functor u p) X Y T

/-- The objectwise Hom-presheaf equivalence is canonical restricted-morphism transport followed
by `ULift.up`. -/
@[simp]
theorem Indexed.canonical.homPresheaf.appEquiv.apply
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U : C} (X Y : (π₁ u p).Fiber U) (T : Over U)
    (φ : ((fiberPseudofunctor (π₁ u p)).presheafHom X Y).obj
      (Opposite.op T)) :
    Indexed.canonical.homPresheaf.appEquiv u p X Y T φ =
      ULift.up
        ((Indexed.canonical.functor u p).mapHom
          T.hom T.hom φ) := sorry

/-- After removing the universe lift, the pointwise Hom-presheaf comparison is the canonical
strictification conjugation. -/
@[simp]
theorem Indexed.canonical.homPresheaf.appEquiv.apply.down
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U : C} (X Y : (π₁ u p).Fiber U) (T : Over U)
    (φ : ((fiberPseudofunctor (π₁ u p)).presheafHom X Y).obj
      (Opposite.op T)) :
    (Indexed.canonical.homPresheaf.appEquiv
        u p X Y T φ).down =
      (Indexed.canonical.comparisonIso u p T.hom X).inv ≫
        (Fiber.chosen.functor u p T.left).map φ ≫
        (Indexed.canonical.comparisonIso u p T.hom Y).hom := sorry

/-- The inverse objectwise Hom-presheaf equivalence removes the universe lift and applies the
inverse canonical restricted-hom equivalence. -/
@[simp]
theorem Indexed.canonical.homPresheaf.appEquiv.symm.apply
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U : C} (X Y : (π₁ u p).Fiber U) (T : Over U)
    (ψ : (((Over.post u).op ⋙
      (fiberPseudofunctor p).presheafHom
        ((Fiber.chosen.functor u p U).obj X)
        ((Fiber.chosen.functor u p U).obj Y) ⋙
          uliftFunctor.{vC}).obj (Opposite.op T))) :
    (Indexed.canonical.homPresheaf.appEquiv u p X Y T).symm ψ =
      (Indexed.canonical.homEquiv
        u p T.hom T.hom).symm ψ.down := sorry

/-- Elementwise naturality of the canonical pointwise Hom-presheaf equivalence in `pullHom`
normal form. -/
theorem Indexed.canonical.homPresheaf.appEquiv.pullHom.down
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U : C} (X Y : (π₁ u p).Fiber U)
    {T₁ T₂ : Over U} (g : T₂ ⟶ T₁)
    (φ : ((fiberPseudofunctor (π₁ u p)).presheafHom X Y).obj
      (Opposite.op T₁)) :
    (Indexed.canonical.homPresheaf.appEquiv u p X Y T₂
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          φ g.left T₂.hom T₂.hom)).down =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        ((Indexed.canonical.homPresheaf.appEquiv
          u p X Y T₁ φ).down)
        (u.map g.left) (u.map T₂.hom) (u.map T₂.hom)
          (Over.post_map_left_comp_hom u g)
          (Over.post_map_left_comp_hom u g) := sorry

/-- The objectwise canonical Hom-presheaf equivalences are natural in the slice object. -/
theorem Indexed.canonical.homPresheaf.appEquiv.naturality
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U : C} (X Y : (π₁ u p).Fiber U) :
    ∀ {T₁ T₂ : (Over U)ᵒᵖ} (α : T₁ ⟶ T₂),
      ((fiberPseudofunctor (π₁ u p)).presheafHom X Y).map α ≫
          (Equiv.toIso
            (Indexed.canonical.homPresheaf.appEquiv
              u p X Y T₂.unop)).hom =
        (Equiv.toIso
          (Indexed.canonical.homPresheaf.appEquiv
            u p X Y T₁.unop)).hom ≫
          (((Over.post u).op ⋙
            (fiberPseudofunctor p).presheafHom
              ((Fiber.chosen.functor u p U).obj X)
              ((Fiber.chosen.functor u p U).obj Y) ⋙
                uliftFunctor.{vC}).map α) := sorry

/-- Hom presheaves in a categorical-pullback fiber are naturally isomorphic to the corresponding
target Hom presheaves pulled back along `Over.post u`. -/
noncomputable def Indexed.canonical.homPresheaf.iso
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U : C} (X Y : (π₁ u p).Fiber U) :
    (fiberPseudofunctor (π₁ u p)).presheafHom X Y ≅
      (Over.post u).op ⋙
        (fiberPseudofunctor p).presheafHom
          ((Fiber.chosen.functor u p U).obj X)
          ((Fiber.chosen.functor u p U).obj Y) ⋙
            uliftFunctor.{vC} :=
  Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.HomPresheaf.iso
    (Indexed.canonical.functor u p) X Y

/-- The forward component of the canonical Hom-presheaf isomorphism is the objectwise Hom
equivalence. -/
@[simp]
theorem Indexed.canonical.homPresheaf.iso.hom.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U : C} (X Y : (π₁ u p).Fiber U) (T : (Over U)ᵒᵖ) :
    (Indexed.canonical.homPresheaf.iso u p X Y).hom.app T =
      (Equiv.toIso
        (Indexed.canonical.homPresheaf.appEquiv
          u p X Y T.unop)).hom := sorry

/-- The inverse component of the canonical Hom-presheaf isomorphism is the inverse objectwise
Hom equivalence. -/
@[simp]
theorem Indexed.canonical.homPresheaf.iso.inv.app
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U : C} (X Y : (π₁ u p).Fiber U) (T : (Over U)ᵒᵖ) :
    (Indexed.canonical.homPresheaf.iso u p X Y).inv.app T =
      (Equiv.toIso
        (Indexed.canonical.homPresheaf.appEquiv
          u p X Y T.unop)).inv := sorry

/-- Sheafness of a Hom presheaf in the pullback fiber is equivalent to sheafness of the
corresponding unlifted target Hom presheaf after precomposition with `Over.post u`. -/
theorem Indexed.canonical.homPresheaf.isSheaf_iff
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    (J : GrothendieckTopology C)
    {U : C} (X Y : (π₁ u p).Fiber U) :
    Presheaf.IsSheaf (J.over U)
        ((fiberPseudofunctor (π₁ u p)).presheafHom X Y) ↔
      Presheaf.IsSheaf (J.over U)
        ((Over.post u).op ⋙
          (fiberPseudofunctor p).presheafHom
            ((Fiber.chosen.functor u p U).obj X)
            ((Fiber.chosen.functor u p U).obj Y)) := sorry

/-- Prestack structure pulls back along the first projection of a categorical pullback whenever
the induced functor on every slice is continuous. -/
theorem Indexed.canonical.homPresheaf.IsPrestack.ofSliceContinuous
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Pseudofunctor.IsPrestack (fiberPseudofunctor p) K]
    (h_continuous : ∀ U : C,
      (Over.post u).IsContinuous (J.over U) (K.over (u.obj U))) :
    Pseudofunctor.IsPrestack (fiberPseudofunctor (π₁ u p)) J := sorry

/-- Prestack structure pulls back along a continuous base functor.  The induced slice
continuity and the categorical-pullback Hom-presheaf comparison are encapsulated by the neutral
indexed-functor API. -/
theorem Indexed.canonical.homPresheaf.IsPrestack.ofIsContinuous
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Pseudofunctor.IsPrestack (fiberPseudofunctor p) K]
    [u.IsContinuous J K] :
    Pseudofunctor.IsPrestack (fiberPseudofunctor (π₁ u p)) J := sorry

end Limits.CategoricalPullback

end CategoryTheory
