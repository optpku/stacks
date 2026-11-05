/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Fiber.Restriction
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber

/-!
# Restriction compatibility of groupoid-fibred morphisms

The fibre functor induced by a morphism of categories fibred in groupoids commutes
with chosen restriction through the canonical comparison of cartesian lifts.
The `Restriction` namespace gives its identity, composition, base-composition,
and Hom-transport laws over an arbitrary base category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open scoped Bicategory

noncomputable section

universe u v w vS

namespace CategoryTheory.FiberedCategoryOver.Groupoids

open Functor Functor.Fiber

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids C}

/-- Applying the total functor of a 1-morphism to a chosen cartesian lift remains cartesian. -/
theorem map_restrict_isCartesian (F : X ⟶ Y) {U Z : C} (x : X.p.Fiber U) (f : Z ⟶ U) :
    Y.p.IsCartesian f ((toFunctor F).map (IsPreFibered.pullbackMap x.property f)) := by
  have aux {a b : X.total} {R T : C} (g : R ⟶ T) (φ : a ⟶ b)
      (h : (toFunctor F ⋙ Y.p).IsHomLift g φ) :
      Y.p.IsCartesian g ((toFunctor F).map φ) := by
    cases h
    exact IsFibered.InGroupoids.all_isCartesian _
  apply aux
  rw [comm F]
  infer_instance

/-- The fibre functor of a 1-morphism commutes with restriction, by uniqueness of cartesian
lifts. -/
def fiberFunctor_restrictObj (F : X ⟶ Y) {U Z : C} (x : X.p.Fiber U) (f : Z ⟶ U) :
    (fiberFunctor F Z).obj (restrictObj x f) ≅
      restrictObj ((fiberFunctor F U).obj x) f :=
  let φ := IsPreFibered.pullbackMap ((fiberFunctor F U).obj x).property f
  let φ' := (toFunctor F).map (IsPreFibered.pullbackMap x.property f)
  let hφ := IsPreFibered.pullbackMap.IsCartesian ((fiberFunctor F U).obj x).property f
  let hφ' := map_restrict_isCartesian F x f
  let e := @IsCartesian.domainUniqueUpToIso _ _ _ _ Y.p _ _ _ _ f φ hφ _ φ' hφ'
  Functor.Fiber.isoMk e
    (@IsCartesian.domainUniqueUpToIso_inv_isHomLift _ _ _ _ Y.p _ _ _ _ f φ hφ _ φ' hφ')

/- Coherence laws for the canonical comparison with chosen restrictions. -/
namespace Restriction

-- Rewriting these comparisons requires reducing the fibre and bicategory wrappers.
set_option backward.isDefEq.respectTransparency false

@[reassoc] theorem comparison_hom_fac {X Y : FiberedCategoryOver.Groupoids C}
    (f : X ⟶ Y) {U V : C} (x : X.p.Fiber U) (g : V ⟶ U) :
    (fiberFunctor_restrictObj f x g).hom.1 ≫
        IsPreFibered.pullbackMap ((fiberFunctor f U).obj x).property g =
      (toFunctor f).map (IsPreFibered.pullbackMap x.property g) := by
  exact @IsCartesian.fac _ _ _ _ Y.p _ _ _ _ g
    (IsPreFibered.pullbackMap ((fiberFunctor f U).obj x).property g)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _
    ((toFunctor f).map (IsPreFibered.pullbackMap x.property g))
    (map_restrict_isCartesian f x g).toIsHomLift

@[reassoc] theorem restriction_hom_fac {X : FiberedCategoryOver.Groupoids C}
    {U V : C} {x y : X.p.Fiber U} (φ : x ⟶ y) (g : V ⟶ U) :
    (restrictHom φ g).1 ≫ IsPreFibered.pullbackMap y.property g =
      IsPreFibered.pullbackMap x.property g ≫ φ.1 := by
  exact @IsCartesian.fac _ _ _ _ X.p _ _ _ _ g
    (IsPreFibered.pullbackMap y.property g)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _
    (IsPreFibered.pullbackMap x.property g ≫ φ.1)
    (@IsHomLift.comp_lift_id_right _ _ _ _ X.p _ _ _ _ _ g
      (IsPreFibered.pullbackMap x.property g)
      (IsPreFibered.pullbackMap.IsCartesian _ _).toIsHomLift φ.1 φ.2)

@[reassoc] theorem restriction_comp_hom_fac {X : FiberedCategoryOver.Groupoids C}
    {U V W : C} (x : X.p.Fiber U) (a : V ⟶ U) (b : W ⟶ V) :
    (restrictObj_comp x a b).hom.1 ≫
        IsPreFibered.pullbackMap x.property (b ≫ a) =
      IsPreFibered.pullbackMap (restrictObj x a).property b ≫
        IsPreFibered.pullbackMap x.property a := by
  letI : X.p.IsCartesian (b ≫ a)
      (IsPreFibered.pullbackMap (restrictObj x a).property b ≫
        IsPreFibered.pullbackMap x.property a) :=
    @IsFibered.comp _ _ _ _ X.p inferInstance _ _ _ b a _ _ _
      (IsPreFibered.pullbackMap (restrictObj x a).property b)
      (IsPreFibered.pullbackMap x.property a)
      (IsPreFibered.pullbackMap.IsCartesian _ _)
      (IsPreFibered.pullbackMap.IsCartesian _ _)
  change IsCartesian.map X.p (b ≫ a)
    (IsPreFibered.pullbackMap x.property (b ≫ a))
    (IsPreFibered.pullbackMap (restrictObj x a).property b ≫
      IsPreFibered.pullbackMap x.property a) ≫ _ = _
  exact
    (@IsCartesian.fac _ _ _ _ X.p _ _ _ _ (b ≫ a)
      (IsPreFibered.pullbackMap x.property (b ≫ a))
      (IsPreFibered.pullbackMap.IsCartesian _ _) _
      (IsPreFibered.pullbackMap (restrictObj x a).property b ≫
        IsPreFibered.pullbackMap x.property a) inferInstance)

theorem restriction_ext {X : FiberedCategoryOver.Groupoids C}
    {U V : C} (y : X.p.Fiber U) (g : V ⟶ U) {z : X.p.Fiber V}
    {φ ψ : z ⟶ restrictObj y g}
    (h : φ.1 ≫ IsPreFibered.pullbackMap y.property g =
      ψ.1 ≫ IsPreFibered.pullbackMap y.property g) : φ = ψ := by
  apply Subtype.ext
  exact @IsCartesian.ext _ _ _ _ X.p _ _ _ _ g
    (IsPreFibered.pullbackMap y.property g)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ φ.1 ψ.1 φ.2 ψ.2 h

theorem comparison_comp {X Y Z : FiberedCategoryOver.Groupoids C}
    (p : X ⟶ Y) (q : Y ⟶ Z) {U V : C} (x : X.p.Fiber U) (g : V ⟶ U) :
    fiberFunctor_restrictObj (p ≫ q) x g =
      (fiberFunctor q V).mapIso (fiberFunctor_restrictObj p x g) ≪≫
        fiberFunctor_restrictObj q ((fiberFunctor p U).obj x) g := by
  apply Iso.ext
  apply restriction_ext
  change (fiberFunctor_restrictObj (p ≫ q) x g).hom.1 ≫ _ =
    ((toFunctor q).map (fiberFunctor_restrictObj p x g).hom.1 ≫
      (fiberFunctor_restrictObj q ((fiberFunctor p U).obj x) g).hom.1) ≫ _
  rw [Category.assoc, comparison_hom_fac, comparison_hom_fac,
    ← Functor.map_comp, comparison_hom_fac]
  rfl

theorem comparison_id {X : FiberedCategoryOver.Groupoids C}
    {U V : C} (x : X.p.Fiber U) (g : V ⟶ U) :
    fiberFunctor_restrictObj (𝟙 X) x g = Iso.refl (restrictObj x g) := by
  apply Iso.ext
  apply restriction_ext
  rw [comparison_hom_fac]
  exact (Category.id_comp _).symm

theorem restriction_comp {X : FiberedCategoryOver.Groupoids C}
    {U V : C} {x y z : X.p.Fiber U} (φ : x ⟶ y) (ψ : y ⟶ z) (g : V ⟶ U) :
    restrictHom (φ ≫ ψ) g = restrictHom φ g ≫ restrictHom ψ g := by
  apply restriction_ext
  change (restrictHom (φ ≫ ψ) g).1 ≫ _ =
    ((restrictHom φ g).1 ≫ (restrictHom ψ g).1) ≫ _
  simp only [Category.assoc, restriction_hom_fac, restriction_hom_fac_assoc]
  rfl

@[reassoc] theorem comparison_restriction {X Y : FiberedCategoryOver.Groupoids C}
    (f : X ⟶ Y) {U V : C} {x y : X.p.Fiber U} (φ : x ⟶ y) (g : V ⟶ U) :
    (fiberFunctor_restrictObj f x g).inv ≫
        (fiberFunctor f V).map (restrictHom φ g) ≫
        (fiberFunctor_restrictObj f y g).hom =
      restrictHom ((fiberFunctor f U).map φ) g := by
  apply (Iso.inv_comp_eq _).mpr
  apply restriction_ext
  change ((toFunctor f).map (restrictHom φ g).1 ≫
    (fiberFunctor_restrictObj f y g).hom.1) ≫ _ =
    ((fiberFunctor_restrictObj f x g).hom.1 ≫
      (restrictHom ((fiberFunctor f U).map φ) g).1) ≫ _
  simp only [Category.assoc, comparison_hom_fac, comparison_hom_fac_assoc,
    restriction_hom_fac]
  change (toFunctor f).map (restrictHom φ g).1 ≫
      (toFunctor f).map (IsPreFibered.pullbackMap y.property g) =
    (toFunctor f).map (IsPreFibered.pullbackMap x.property g) ≫ (toFunctor f).map φ.1
  simpa only [Functor.map_comp] using
    congrArg (toFunctor f).map (restriction_hom_fac φ g)

theorem comparison_base_comp {X Y : FiberedCategoryOver.Groupoids C}
    (f : X ⟶ Y) {U V W : C} (x : X.p.Fiber U) (a : V ⟶ U) (b : W ⟶ V) :
    (fiberFunctor f W).mapIso (restrictObj_comp x a b) ≪≫
        fiberFunctor_restrictObj f x (b ≫ a) =
      fiberFunctor_restrictObj f (restrictObj x a) b ≪≫
        restrictIso (fiberFunctor_restrictObj f x a) b ≪≫
        restrictObj_comp ((fiberFunctor f U).obj x) a b := by
  apply Iso.ext
  apply restriction_ext
  change ((toFunctor f).map (restrictObj_comp x a b).hom.1 ≫
      (fiberFunctor_restrictObj f x (b ≫ a)).hom.1) ≫ _ =
    ((fiberFunctor_restrictObj f (restrictObj x a) b).hom.1 ≫
      (restrictHom (fiberFunctor_restrictObj f x a).hom b).1 ≫
      (restrictObj_comp ((fiberFunctor f U).obj x) a b).hom.1) ≫ _
  have hx := restriction_comp_hom_fac x a b
  have hy := restriction_comp_hom_fac ((fiberFunctor f U).obj x) a b
  simp only [Category.assoc, comparison_hom_fac, comparison_hom_fac_assoc,
    hy, restriction_hom_fac_assoc, ← Functor.map_comp, hx]

theorem hom_transport_base_comp {X Y : FiberedCategoryOver.Groupoids C}
    (f : X ⟶ Y) {U V W : C} (x y : X.p.Fiber U) (a : V ⟶ U) (b : W ⟶ V)
    {d : W ⟶ U} (h : b ≫ a = d) (φ : restrictObj x a ⟶ restrictObj y a) :
    (fiberFunctor_restrictObj f x d).inv ≫
        (fiberFunctor f W).map
          ((restrictObj_comp x a b ≪≫ restrictObj_eq x h).inv ≫
            restrictHom φ b ≫ (restrictObj_comp y a b ≪≫ restrictObj_eq y h).hom) ≫
        (fiberFunctor_restrictObj f y d).hom =
      (restrictObj_comp ((fiberFunctor f U).obj x) a b ≪≫
          restrictObj_eq ((fiberFunctor f U).obj x) h).inv ≫
        restrictHom ((fiberFunctor_restrictObj f x a).inv ≫
          (fiberFunctor f V).map φ ≫ (fiberFunctor_restrictObj f y a).hom) b ≫
        (restrictObj_comp ((fiberFunctor f U).obj y) a b ≪≫
          restrictObj_eq ((fiberFunctor f U).obj y) h).hom := by
  subst d
  simp only [restrictObj_eq, eqToIso_refl, Iso.trans_hom, Iso.trans_inv,
    Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp]
  have he (z : X.p.Fiber U) :
      fiberFunctor_restrictObj f z (b ≫ a) =
        ((fiberFunctor f W).mapIso (restrictObj_comp z a b)).symm ≪≫
          fiberFunctor_restrictObj f (restrictObj z a) b ≪≫
            restrictIso (fiberFunctor_restrictObj f z a) b ≪≫
              restrictObj_comp ((fiberFunctor f U).obj z) a b := by
    apply Iso.ext
    apply (Iso.eq_inv_comp _).mpr
    exact congrArg Iso.hom (comparison_base_comp f z a b)
  rw [he x, he y]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, restriction_comp,
    Category.assoc, Iso.map_hom_inv_id_assoc,
    comparison_restriction_assoc]
  rfl

theorem hom_transport_comp {X Y Z : FiberedCategoryOver.Groupoids C}
    (p : X ⟶ Y) (q : Y ⟶ Z) {U V : C} (x y : X.p.Fiber U) (g : V ⟶ U)
    (φ : restrictObj x g ⟶ restrictObj y g) :
    (fiberFunctor_restrictObj (p ≫ q) x g).inv ≫
        (fiberFunctor (p ≫ q) V).map φ ≫
        (fiberFunctor_restrictObj (p ≫ q) y g).hom =
      (fiberFunctor_restrictObj q ((fiberFunctor p U).obj x) g).inv ≫
        (fiberFunctor q V).map ((fiberFunctor_restrictObj p x g).inv ≫
          (fiberFunctor p V).map φ ≫ (fiberFunctor_restrictObj p y g).hom) ≫
        (fiberFunctor_restrictObj q ((fiberFunctor p U).obj y) g).hom := by
  rw [comparison_comp, comparison_comp]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  rfl

end Restriction

end CategoryTheory.FiberedCategoryOver.Groupoids
