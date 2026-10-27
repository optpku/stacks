/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Cleavage
public import ReasLib.CategoryTheory.Fibered.CategoryOver.HomPresheaf.Local
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Extension
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.LocalEquivalence

/-!
# Hom-presheaf extensions for morphisms of fibered categories

This file is the fibered-category interface to the generic extension API for
strong transformations.  It keeps the hypotheses at the Hom-presheaf and
prestack levels, without imposing stackification or essential-surjectivity
conditions which are irrelevant to extending morphisms between image objects.

The Homwise local-equivalence predicate is the fixed-universe view of the
canonical owner `CartesianBasedFunctor.Homwise.IsLocalEquivalence`; the
generic strong-transformation extension is reached through the bridge
`Homwise.IsLocalEquivalence.toStrongTrans`.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Opposite

namespace FiberedCategoryOver.Hom

variable {C : Type u} [Category.{v} C]
variable {X Y Z : FiberedCategoryOver.{u, v, uS, vS} C}
variable {J : GrothendieckTopology C}

/-- A morphism of fibered categories is locally equivalent on Hom-presheaves when every
canonical Hom-presheaf map is locally injective and locally surjective.
This is the fixed-universe view of the heterogeneous cartesian-functor owner. -/
abbrev Homwise.IsLocalEquivalence
    (J : GrothendieckTopology C) (F : X ⟶ Y) : Prop :=
  CartesianBasedFunctor.Homwise.IsLocalEquivalence J
    (FiberedCategoryOver.toCartesianBasedFunctor F)

/-- The cartesian-functor Hom map is the fixed-universe Hom map with its values lifted.
Both constructions use the same chosen cleavages and reindexing comparisons. -/
theorem presheafHomMap.whiskerRight_ulift
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) :
    Functor.whiskerRight (presheafHomMap F x y) uliftFunctor.{vS, vS} =
      CartesianBasedFunctor.HomPresheaf.Chosen.map
        (FiberedCategoryOver.toCartesianBasedFunctor F) x y := by
  rfl

/-- Removing the valuewise `ULift` identifies the cartesian-functor Hom map with the
Hom map of the associated strong transformation, as arrows of presheaves. -/
noncomputable def presheafHomMap.chosenArrowIso
    (F : X ⟶ Y) {U : C} (x y : X.p.Fiber U) :
    Arrow.mk (CartesianBasedFunctor.HomPresheaf.Chosen.map
        (FiberedCategoryOver.toCartesianBasedFunctor F) x y) ≅
      Arrow.mk (presheafHomMap F x y) :=
  Arrow.isoMk
    (Functor.isoWhiskerLeft _ uliftFunctorTrivial ≪≫ Functor.rightUnitor _)
    (Functor.isoWhiskerLeft _ uliftFunctorTrivial ≪≫ Functor.rightUnitor _)
    (by
      rw [← presheafHomMap.whiskerRight_ulift]
      ext W δ
      rfl)

/-- A Homwise local equivalence of fibered categories is a Homwise local equivalence of the
associated strong transformation of fiber pseudofunctors.  This bridges the cartesian-functor
owner to the generic strong-transformation extension API. -/
theorem Homwise.IsLocalEquivalence.toStrongTrans
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F) :
    Pseudofunctor.StrongTrans.Homwise.IsLocalEquivalence
      (FiberedCategoryOver.strongTrans F) J := by
  intro U x y
  exact ((J.over U).W.arrow_mk_iso_iff
    (presheafHomMap.chosenArrowIso F x y)).1
      (Presheaf.LocallyBijective.mem_W _ _ (hF x y).1 (hF x y).2)

/-- When slice localizing classes coincide with locally bijective maps at the value universe,
Homwise local equivalence is equivalent to membership of every Hom map in those classes. -/
theorem Homwise.isLocalEquivalence_iff
    (J : GrothendieckTopology C) (F : X ⟶ Y)
    [∀ U : C, (J.over U).WEqualsLocallyBijective (Type vS)] :
    Homwise.IsLocalEquivalence J F ↔
      ∀ {U : C} (x y : X.p.Fiber U),
        (J.over U).W (presheafHomMap F x y) := by
  constructor
  · intro hF
    exact hF.toStrongTrans
  · intro hF U x y
    exact ((J.over U).W_iff_isLocallyBijective _).1
      (((J.over U).W.arrow_mk_iso_iff
        (presheafHomMap.chosenArrowIso F x y)).2 (hF x y))

/-- The strong-transformation condition reflects to the cartesian-functor owner whenever
the slice localizing classes are locally bijective maps at the value universe. -/
theorem Homwise.IsLocalEquivalence.ofStrongTrans
    {F : X ⟶ Y}
    [∀ U : C, (J.over U).WEqualsLocallyBijective (Type vS)]
    (hF : Pseudofunctor.StrongTrans.Homwise.IsLocalEquivalence
      (FiberedCategoryOver.strongTrans F) J) :
    Homwise.IsLocalEquivalence J F :=
  (Homwise.isLocalEquivalence_iff J F).2 hF

/-- A Homwise local equivalence is Homwise locally surjective. -/
theorem Homwise.IsLocalEquivalence.isLocallySurjective
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F) :
    Homwise.IsLocallySurjective J F := sorry

/-- Homwise local equivalences are closed under composition. -/
theorem Homwise.IsLocalEquivalence.comp
    {W : FiberedCategoryOver.{u, v, uS, vS} C}
    {F : X ⟶ Y} {G : Y ⟶ W}
    (hF : Homwise.IsLocalEquivalence J F)
    (hG : Homwise.IsLocalEquivalence J G) :
    Homwise.IsLocalEquivalence J (F ≫ G) := sorry

/-- An equivalence over the base is a local equivalence on every canonical Hom-presheaf. -/
theorem Homwise.IsLocalEquivalence.of_isEquivalence
    (F : X ⟶ Y) (hF : (FiberedCategoryOver.toBasedFunctor F).IsEquivalence) :
    Homwise.IsLocalEquivalence J F := sorry

/-- Precomposition by an equivalence over the base preserves Homwise local equivalence. -/
theorem Homwise.IsLocalEquivalence.comp_left_of_isEquivalence
    {W : FiberedCategoryOver.{u, v, uS, vS} C}
    (E : X ⟶ Y) (hE : (FiberedCategoryOver.toBasedFunctor E).IsEquivalence)
    (G : Y ⟶ W) (hG : Homwise.IsLocalEquivalence J G) :
    Homwise.IsLocalEquivalence J (E ≫ G) := sorry

/-- Postcomposition by an equivalence over the base preserves Homwise local equivalence. -/
theorem Homwise.IsLocalEquivalence.comp_right_of_isEquivalence
    {W : FiberedCategoryOver.{u, v, uS, vS} C}
    (F : X ⟶ Y) (hF : Homwise.IsLocalEquivalence J F)
    (E : Y ⟶ W) (hE : (FiberedCategoryOver.toBasedFunctor E).IsEquivalence) :
    Homwise.IsLocalEquivalence J (F ≫ E) := sorry

/-- Homwise local equivalence reflects across postcomposition by an equivalence over the base. -/
theorem Homwise.IsLocalEquivalence.of_comp_right_isEquivalence
    {W : FiberedCategoryOver.{u, v, uS, vS} C}
    (F : X ⟶ Y) (E : Y ⟶ W)
    (hE : (FiberedCategoryOver.toBasedFunctor E).IsEquivalence)
    (hFE : Homwise.IsLocalEquivalence J (F ≫ E)) :
    Homwise.IsLocalEquivalence J F := sorry

/-- Transport Homwise local equivalence along an isomorphism of parallel morphisms of
fibered categories. -/
theorem Homwise.IsLocalEquivalence.of_iso
    {F G : X ⟶ Y} (e : F ≅ G)
    (hF : Homwise.IsLocalEquivalence J F) :
    Homwise.IsLocalEquivalence J G := sorry

/-- Isomorphic parallel morphisms are Homwise local equivalences simultaneously. -/
theorem Homwise.isLocalEquivalence_iff_of_iso
    {F G : X ⟶ Y} (e : F ≅ G) :
    Homwise.IsLocalEquivalence J F ↔ Homwise.IsLocalEquivalence J G := sorry

/-- The canonical extension of the Hom-presheaf map of `G` along the Homwise local
equivalence `F`. -/
noncomputable def Homwise.IsLocalEquivalence.extension
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F)
    (G : X ⟶ Z)
    [(Functor.fiberPseudofunctor Z.p).IsPrestack J]
    {U : C} (x y : X.p.Fiber U) :
    (Functor.fiberPseudofunctor Y.p).presheafHom
          ((FiberedCategoryOver.fiberFunctor F U).obj x)
          ((FiberedCategoryOver.fiberFunctor F U).obj y) ⟶
      (Functor.fiberPseudofunctor Z.p).presheafHom
          ((FiberedCategoryOver.fiberFunctor G U).obj x)
          ((FiberedCategoryOver.fiberFunctor G U).obj y) :=
  Pseudofunctor.StrongTrans.Homwise.IsLocalEquivalence.extension hF.toStrongTrans
    (FiberedCategoryOver.strongTrans G) x y

/-- Precomposition with the Hom-presheaf map of `F` recovers the Hom-presheaf map of `G`. -/
theorem Homwise.IsLocalEquivalence.Extension.fac
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F)
    (G : X ⟶ Z)
    [(Functor.fiberPseudofunctor Z.p).IsPrestack J]
    {U : C} (x y : X.p.Fiber U) :
    presheafHomMap F x y ≫ hF.extension G x y =
      presheafHomMap G x y := sorry

/-- A Hom-presheaf map satisfying the defining factorization is the canonical extension. -/
theorem Homwise.IsLocalEquivalence.Extension.ext
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F)
    (G : X ⟶ Z)
    [(Functor.fiberPseudofunctor Z.p).IsPrestack J]
    {U : C} (x y : X.p.Fiber U)
    (e :
      (Functor.fiberPseudofunctor Y.p).presheafHom
            ((FiberedCategoryOver.fiberFunctor F U).obj x)
            ((FiberedCategoryOver.fiberFunctor F U).obj y) ⟶
        (Functor.fiberPseudofunctor Z.p).presheafHom
            ((FiberedCategoryOver.fiberFunctor G U).obj x)
            ((FiberedCategoryOver.fiberFunctor G U).obj y))
    (he : presheafHomMap F x y ≫ e = presheafHomMap G x y) :
    e = hF.extension G x y := sorry

/-- The canonical Hom-presheaf extension is the unique map satisfying its defining
factorization through `presheafHomMap F x y`. -/
theorem Homwise.IsLocalEquivalence.Extension.existsUnique
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F)
    (G : X ⟶ Z)
    [(Functor.fiberPseudofunctor Z.p).IsPrestack J]
    {U : C} (x y : X.p.Fiber U) :
    ∃! e :
      (Functor.fiberPseudofunctor Y.p).presheafHom
            ((FiberedCategoryOver.fiberFunctor F U).obj x)
            ((FiberedCategoryOver.fiberFunctor F U).obj y) ⟶
        (Functor.fiberPseudofunctor Z.p).presheafHom
            ((FiberedCategoryOver.fiberFunctor G U).obj x)
            ((FiberedCategoryOver.fiberFunctor G U).obj y),
      presheafHomMap F x y ≫ e = presheafHomMap G x y := sorry

/-- Evaluation of the canonical extension on the identity slice gives a map between the
corresponding image objects in the target fiber. -/
noncomputable def Homwise.IsLocalEquivalence.Extension.map
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F)
    (G : X ⟶ Z)
    [(Functor.fiberPseudofunctor Z.p).IsPrestack J]
    {U : C} {x y : X.p.Fiber U}
    (f : (FiberedCategoryOver.fiberFunctor F U).obj x ⟶
      (FiberedCategoryOver.fiberFunctor F U).obj y) :
    (FiberedCategoryOver.fiberFunctor G U).obj x ⟶
      (FiberedCategoryOver.fiberFunctor G U).obj y :=
  Pseudofunctor.StrongTrans.Homwise.IsLocalEquivalence.Extension.map hF.toStrongTrans
    (FiberedCategoryOver.strongTrans G) f

/-- Evaluating the Hom extension after applying fiber reindexing to a morphism agrees with
reindexing its identity-slice extension. -/
theorem Homwise.IsLocalEquivalence.Extension.appMap
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F)
    (G : X ⟶ Z)
    [(Functor.fiberPseudofunctor Z.p).IsPrestack J]
    {U V : C} (f : V ⟶ U) {x y : X.p.Fiber U}
    (g : (FiberedCategoryOver.fiberFunctor F U).obj x ⟶
      (FiberedCategoryOver.fiberFunctor F U).obj y) :
    (hF.extension G x y).app (op (Over.mk f))
        (((Functor.fiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map g) =
      ((Functor.fiberPseudofunctor Z.p).map f.op.toLoc).toFunctor.map
        (Homwise.IsLocalEquivalence.Extension.map hF G g) := sorry

/-- The Hom extension is compatible with the canonical comparison isomorphisms between
fiber-functor images of reindexed objects and pseudofunctor reindexing. -/
theorem Homwise.IsLocalEquivalence.Extension.appReindexIso
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F)
    (G : X ⟶ Z)
    [(Functor.fiberPseudofunctor Z.p).IsPrestack J]
    {U V : C} (f : V ⟶ U) {x y : X.p.Fiber U}
    (g : (FiberedCategoryOver.fiberFunctor F V).obj
          (f⁎[X.chosenCleavage] x) ⟶
        (FiberedCategoryOver.fiberFunctor F V).obj
          (f⁎[X.chosenCleavage] y)) :
    (hF.extension G x y).app (op (Over.mk f))
        ((FiberedCategoryOver.Reindex.mapIso F f x).hom ≫ g ≫
          (FiberedCategoryOver.Reindex.mapIso F f y).inv) =
      (FiberedCategoryOver.Reindex.mapIso G f x).hom ≫
        Homwise.IsLocalEquivalence.Extension.map hF G g ≫
          (FiberedCategoryOver.Reindex.mapIso G f y).inv := sorry

/-- The extended fiber map agrees with `G` on morphisms in the image of `F`. -/
theorem Homwise.IsLocalEquivalence.Extension.map_onImage
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F)
    (G : X ⟶ Z)
    [(Functor.fiberPseudofunctor Z.p).IsPrestack J]
    {U : C} {x y : X.p.Fiber U} (f : x ⟶ y) :
    Homwise.IsLocalEquivalence.Extension.map hF G
        ((FiberedCategoryOver.fiberFunctor F U).map f) =
      (FiberedCategoryOver.fiberFunctor G U).map f := sorry

/-- The extended fiber map preserves identities. -/
theorem Homwise.IsLocalEquivalence.Extension.map_id
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F)
    (G : X ⟶ Z)
    [(Functor.fiberPseudofunctor Z.p).IsPrestack J]
    {U : C} (x : X.p.Fiber U) :
    Homwise.IsLocalEquivalence.Extension.map hF G
        (𝟙 ((FiberedCategoryOver.fiberFunctor F U).obj x)) =
      𝟙 ((FiberedCategoryOver.fiberFunctor G U).obj x) := sorry

/-- The extended fiber map preserves arbitrary compositions between image objects. -/
theorem Homwise.IsLocalEquivalence.Extension.map_comp
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F)
    (G : X ⟶ Z)
    [(Functor.fiberPseudofunctor Z.p).IsPrestack J]
    {U : C} {x y z : X.p.Fiber U}
    (f : (FiberedCategoryOver.fiberFunctor F U).obj x ⟶
      (FiberedCategoryOver.fiberFunctor F U).obj y)
    (g : (FiberedCategoryOver.fiberFunctor F U).obj y ⟶
      (FiberedCategoryOver.fiberFunctor F U).obj z) :
    Homwise.IsLocalEquivalence.Extension.map hF G (f ≫ g) =
      Homwise.IsLocalEquivalence.Extension.map hF G f ≫
        Homwise.IsLocalEquivalence.Extension.map hF G g := sorry

/-- The Hom extension is natural under postcomposition at its target endpoint. -/
theorem Homwise.IsLocalEquivalence.Extension.postcomp
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F)
    (G : X ⟶ Z)
    [(Functor.fiberPseudofunctor Z.p).IsPrestack J]
    {U : C} {x y z : X.p.Fiber U}
    (f : (FiberedCategoryOver.fiberFunctor F U).obj y ⟶
      (FiberedCategoryOver.fiberFunctor F U).obj z) :
    hF.extension G x y ≫
        Pseudofunctor.PresheafHom.Postcomp.map
          (Functor.fiberPseudofunctor Z.p)
          (Homwise.IsLocalEquivalence.Extension.map hF G f) =
      Pseudofunctor.PresheafHom.Postcomp.map
          (Functor.fiberPseudofunctor Y.p) f ≫
        hF.extension G x z := sorry

/-- The Hom extension is natural under precomposition at its source endpoint. -/
theorem Homwise.IsLocalEquivalence.Extension.precomp
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F)
    (G : X ⟶ Z)
    [(Functor.fiberPseudofunctor Z.p).IsPrestack J]
    {U : C} {x y z : X.p.Fiber U}
    (f : (FiberedCategoryOver.fiberFunctor F U).obj x ⟶
      (FiberedCategoryOver.fiberFunctor F U).obj y) :
    hF.extension G y z ≫
        Pseudofunctor.PresheafHom.Precomp.map
          (Functor.fiberPseudofunctor Z.p)
          (Homwise.IsLocalEquivalence.Extension.map hF G f) =
      Pseudofunctor.PresheafHom.Precomp.map
          (Functor.fiberPseudofunctor Y.p) f ≫
        hF.extension G x z := sorry

/-- The extended fiber map preserves commutative squares between image objects. -/
theorem Homwise.IsLocalEquivalence.Extension.map_square
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F)
    (G : X ⟶ Z)
    [(Functor.fiberPseudofunctor Z.p).IsPrestack J]
    {U : C} {x₁ x₂ y₁ y₂ : X.p.Fiber U}
    (f₁ : (FiberedCategoryOver.fiberFunctor F U).obj x₁ ⟶
      (FiberedCategoryOver.fiberFunctor F U).obj y₁)
    (gₓ : (FiberedCategoryOver.fiberFunctor F U).obj x₁ ⟶
      (FiberedCategoryOver.fiberFunctor F U).obj x₂)
    (gᵧ : (FiberedCategoryOver.fiberFunctor F U).obj y₁ ⟶
      (FiberedCategoryOver.fiberFunctor F U).obj y₂)
    (f₂ : (FiberedCategoryOver.fiberFunctor F U).obj x₂ ⟶
      (FiberedCategoryOver.fiberFunctor F U).obj y₂)
    (h : f₁ ≫ gᵧ = gₓ ≫ f₂) :
    Homwise.IsLocalEquivalence.Extension.map hF G f₁ ≫
        Homwise.IsLocalEquivalence.Extension.map hF G gᵧ =
      Homwise.IsLocalEquivalence.Extension.map hF G gₓ ≫
        Homwise.IsLocalEquivalence.Extension.map hF G f₂ := sorry

/-- Changing source objects by isomorphisms conjugates the extended fiber map by their
images under the target morphism. -/
theorem Homwise.IsLocalEquivalence.Extension.map_transport
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F)
    (G : X ⟶ Z)
    [(Functor.fiberPseudofunctor Z.p).IsPrestack J]
    {U : C} {x x' y y' : X.p.Fiber U}
    (eₓ : x ≅ x') (eᵧ : y ≅ y')
    (f : (FiberedCategoryOver.fiberFunctor F U).obj x' ⟶
      (FiberedCategoryOver.fiberFunctor F U).obj y') :
    Homwise.IsLocalEquivalence.Extension.map hF G
        ((FiberedCategoryOver.fiberFunctor F U).map eₓ.hom ≫ f ≫
          (FiberedCategoryOver.fiberFunctor F U).map eᵧ.inv) =
      (FiberedCategoryOver.fiberFunctor G U).map eₓ.hom ≫
        Homwise.IsLocalEquivalence.Extension.map hF G f ≫
          (FiberedCategoryOver.fiberFunctor G U).map eᵧ.inv := sorry

/-- The Hom extension packaged as a functor from the category induced on the source objects by
the fiber functor of `F`. -/
noncomputable def Homwise.IsLocalEquivalence.Extension.functor
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F)
    (G : X ⟶ Z)
    [(Functor.fiberPseudofunctor Z.p).IsPrestack J]
    (U : C) :
    InducedCategory (Y.p.Fiber U)
        (FiberedCategoryOver.fiberFunctor F U).obj ⥤
      Z.p.Fiber U :=
  Pseudofunctor.StrongTrans.Homwise.IsLocalEquivalence.Extension.functor hF.toStrongTrans
    (FiberedCategoryOver.strongTrans G) U

/-- The extension functor maps an induced morphism by identity-slice evaluation of the
canonical Hom-presheaf extension. -/
theorem Homwise.IsLocalEquivalence.Extension.functor_map
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F)
    (G : X ⟶ Z)
    [(Functor.fiberPseudofunctor Z.p).IsPrestack J]
    (U : C)
    {x y : InducedCategory (Y.p.Fiber U)
      (FiberedCategoryOver.fiberFunctor F U).obj}
    (f : x ⟶ y) :
    (Homwise.IsLocalEquivalence.Extension.functor hF G U).map f =
      Homwise.IsLocalEquivalence.Extension.map hF G f.hom := sorry

/-- Restricting the extension functor along the canonical factor of the source fiber functor
recovers the fiber functor of `G`. -/
theorem Homwise.IsLocalEquivalence.Extension.functor_toInducedComp
    {F : X ⟶ Y} (hF : Homwise.IsLocalEquivalence J F)
    (G : X ⟶ Z)
    [(Functor.fiberPseudofunctor Z.p).IsPrestack J]
    (U : C) :
    (FiberedCategoryOver.fiberFunctor F U).toInduced ⋙
        Homwise.IsLocalEquivalence.Extension.functor hF G U =
      FiberedCategoryOver.fiberFunctor G U := sorry

end FiberedCategoryOver.Hom

end CategoryTheory
