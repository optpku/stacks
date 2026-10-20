/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.KernelPair.Points
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Iso
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Bicategorical
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base

/-!
# Representation of a presheaf kernel pair

Both functors between the literal point presheaf and the explicit pseudo-pullback
are defined on objects and morphisms. The comparison cells use the displayed
base identifications and the two actual presheaf-component maps.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Bicategory

noncomputable section

universe u v

namespace CategoryTheory.FiberedCategoryOver.Groupoids

/-- Pair two displayed morphisms into the actual relative product over the
universe-closed identity fibration. -/
def pairOverBase {C : Type u} [Category.{v} C]
    {A X : FiberedCategoryOver.Groupoids.{u, v, max u v, v} C}
    (f g : A ⟶ X) : A ⟶ TwoFibreProduct.apex X.baseProjection X.baseProjection :=
  ofBasedFunctor
    { toFunctor :=
        { obj := fun a ↦
            BasedCategory.PseudoPullback.mk X.baseProjection.hom X.baseProjection.hom
              (A.p.obj a)
              { fst := ⟨(toFunctor f).obj a, f.hom.w_obj a⟩
                snd := ⟨(toFunctor g).obj a, g.hom.w_obj a⟩
                iso := Functor.Fiber.isoMk
                  ((baseSection C).mapIso
                    (eqToIso ((f.hom.w_obj a).trans (g.hom.w_obj a).symm)))
                  (hhom := by sorry) }
          map := fun φ ↦
            BasedCategory.PseudoPullback.Hom.mk (A.p.map φ)
              ((toFunctor f).map φ) sorry
              ((toFunctor g).map φ) sorry sorry
          map_id := sorry
          map_comp := sorry }
      w := sorry }

end CategoryTheory.FiberedCategoryOver.Groupoids

namespace CategoryTheory.FiberedCategoryOver.Groupoids.PresheafKernelPair

variable {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type v)
variable {X : FiberedCategoryOver.Groupoids.{u, v, max u v, v} C}
variable (f : ofPresheaf P ⟶ X)

/-- Read the element stored by a fibre object, transporting only its supplied base equality. -/
def value (T : C) (a : (ofPresheaf P).p.Fiber T) : P.obj (op T) :=
  FiberedCategoryOver.Sets.ofPresheaf.fiberToValue P T a

/-- Normalize a presheaf fibre object using explicit opposite category-of-elements arrows.
Both base maps are the isomorphism supplied by the fibre object's base equality. -/
def pointValueIso (T : C) (a : (ofPresheaf P).p.Fiber T) :
    point P T (value P T a) ≅ a where
  hom := Functor.Fiber.Hom.mk
    (CategoryOfElements.homMk a.1.unop
      (⟨op T, value P T a⟩ : P.Elements)
      (eqToHom (congrArg op a.2)) rfl).op sorry
  inv := Functor.Fiber.Hom.mk
    (CategoryOfElements.homMk
      (⟨op T, value P T a⟩ : P.Elements) a.1.unop
      (eqToHom (congrArg op a.2.symm)) sorry).op sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Read the two actual fibre objects and conjugate their supplied comparison by normalization. -/
def pointOfPullback (a : (BasedCategory.PseudoPullback f.hom f.hom).obj) :
    Point P f (BasedCategory.PseudoPullback.baseObj a) where
  fst := value P _ (BasedCategory.PseudoPullback.fiberObj a).fst
  snd := value P _ (BasedCategory.PseudoPullback.fiberObj a).snd
  iso :=
    (fiberFunctor f _).mapIso
        (pointValueIso P _ (BasedCategory.PseudoPullback.fiberObj a).fst) ≪≫
      (BasedCategory.PseudoPullback.fiberObj a).iso ≪≫
        ((fiberFunctor f _).mapIso
          (pointValueIso P _ (BasedCategory.PseudoPullback.fiberObj a).snd)).symm

/-- A pseudo-pullback arrow induces the presheaf equality over its displayed base map. -/
theorem pointOfPullback_naturality
    {a b : (BasedCategory.PseudoPullback f.hom f.hom).obj} (φ : a ⟶ b) :
    (presheaf P f).map (BasedCategory.PseudoPullback.baseMap φ).op
        (pointOfPullback P f b) = pointOfPullback P f a := sorry

/-- The forward comparison records the literal pair of points and its vertical isomorphism. -/
def forward :
    BasedCategory.PseudoPullback f.hom f.hom ⥤ᵇ
      (ofPresheaf (presheaf P f)).toBasedCategory where
  toFunctor :=
    { obj := fun a ↦ op ⟨op (BasedCategory.PseudoPullback.baseObj a), pointOfPullback P f a⟩
      map := fun {a b} φ ↦
        (CategoryOfElements.homMk
          (⟨op (BasedCategory.PseudoPullback.baseObj b), pointOfPullback P f b⟩ :
            (presheaf P f).Elements)
          (⟨op (BasedCategory.PseudoPullback.baseObj a), pointOfPullback P f a⟩ :
            (presheaf P f).Elements)
          (BasedCategory.PseudoPullback.baseMap φ).op
          (pointOfPullback_naturality P f φ)).op
      map_id := sorry
      map_comp := sorry }
  w := sorry

/-- The reverse comparison stores the two specified points and the given comparison directly. -/
def backward :
    (ofPresheaf (presheaf P f)).toBasedCategory ⥤ᵇ
      BasedCategory.PseudoPullback f.hom f.hom where
  toFunctor :=
    { obj := fun a ↦
        BasedCategory.PseudoPullback.mk f.hom f.hom a.unop.1.unop
          { fst := point P _ a.unop.2.fst
            snd := point P _ a.unop.2.snd
            iso := a.unop.2.iso }
      map := fun {a b} φ ↦
        BasedCategory.PseudoPullback.Hom.mk φ.unop.1.unop
          (CategoryOfElements.homMk
            (⟨b.unop.1, b.unop.2.fst⟩ : P.Elements)
            (⟨a.unop.1, a.unop.2.fst⟩ : P.Elements)
            φ.unop.1
            (congrArg (fun q : Point P f a.unop.1.unop ↦ q.fst) φ.unop.2)).op sorry
          (CategoryOfElements.homMk
            (⟨b.unop.1, b.unop.2.snd⟩ : P.Elements)
            (⟨a.unop.1, a.unop.2.snd⟩ : P.Elements)
            φ.unop.1
            (congrArg (fun q : Point P f a.unop.1.unop ↦ q.snd) φ.unop.2)).op sorry
          sorry
      map_id := sorry
      map_comp := sorry }
  w := sorry

/-- The reverse-forward comparison retains the two supplied normalization maps. -/
def backwardForwardIso (a : (BasedCategory.PseudoPullback f.hom f.hom).obj) :
    (backward P f).obj ((forward P f).obj a) ≅ a :=
  BasedCategory.PseudoPullback.mkIso
    (Iso.refl (BasedCategory.PseudoPullback.baseObj a))
    (Functor.Fiber.fiberInclusion.mapIso
      (pointValueIso P _ (BasedCategory.PseudoPullback.fiberObj a).fst))
    (Functor.Fiber.fiberInclusion.mapIso
      (pointValueIso P _ (BasedCategory.PseudoPullback.fiberObj a).snd))
    sorry sorry sorry

/-- The forward-reverse comparison has identity base arrows in both directions. -/
def forwardBackwardIso (a : (ofPresheaf (presheaf P f)).total) :
    (forward P f).obj ((backward P f).obj a) ≅ a where
  hom := (CategoryOfElements.homMk a.unop
    ((forward P f).obj ((backward P f).obj a)).unop (𝟙 a.unop.1) sorry).op
  inv := (CategoryOfElements.homMk
    ((forward P f).obj ((backward P f).obj a)).unop a.unop (𝟙 a.unop.1) sorry).op
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Explicit based quasi-inverse data for the two actual comparison functors. -/
def quasiInverse : BasedFunctor.QuasiInverse (forward P f) where
  inverse := backward P f
  unitIso := BasedNatIso.ofComponents
    (fun a ↦ (backwardForwardIso P f a).symm) sorry sorry
  counitIso := BasedNatIso.ofComponents
    (forwardBackwardIso P f) sorry sorry

/-- The kernel pair is represented by its actual point-and-vertical-isomorphism presheaf.
No map is selected from a chosen bilimit or an admitted equivalence theorem. -/
def equivalence :
    TwoFibreProduct.apex f f ≌ ofPresheaf (presheaf P f) :=
  Bicategory.InducedBicategory.equivalenceMk
    (quasiInverse P f).toEquivalence

/-- The first projection comparison is the given fibre-object normalization. -/
def fstIso :
    (equivalence P f).hom ≫
        (FiberedCategoryOver.Sets.toGroupoids C).map
          ((FiberedCategoryOver.Sets.ofPresheaf C).map (fst P f)) ≅
      TwoFibreProduct.fst f f :=
  Bicategory.InducedBicategory.isoMk
    (BasedNatIso.ofComponents
      (fun a ↦ Functor.Fiber.fiberInclusion.mapIso
        (pointValueIso P _ (BasedCategory.PseudoPullback.fiberObj a).fst))
      sorry sorry)

/-- The second projection comparison uses the second given fibre-object normalization. -/
def sndIso :
    (equivalence P f).hom ≫
        (FiberedCategoryOver.Sets.toGroupoids C).map
          ((FiberedCategoryOver.Sets.ofPresheaf C).map (snd P f)) ≅
      TwoFibreProduct.snd f f :=
  Bicategory.InducedBicategory.isoMk
    (BasedNatIso.ofComponents
      (fun a ↦ Functor.Fiber.fiberInclusion.mapIso
        (pointValueIso P _ (BasedCategory.PseudoPullback.fiberObj a).snd))
      sorry sorry)

/-- The universal comparison on the represented kernel pair has its supplied iso as component. -/
def comparisonIso :
    (FiberedCategoryOver.Sets.toGroupoids C).map
        ((FiberedCategoryOver.Sets.ofPresheaf C).map (fst P f)) ≫ f ≅
      (FiberedCategoryOver.Sets.toGroupoids C).map
        ((FiberedCategoryOver.Sets.ofPresheaf C).map (snd P f)) ≫ f :=
  Bicategory.InducedBicategory.isoMk
    (BasedNatIso.ofComponents
      (fun a ↦ Functor.Fiber.fiberInclusion.mapIso a.unop.2.iso)
      sorry sorry)

end CategoryTheory.FiberedCategoryOver.Groupoids.PresheafKernelPair
