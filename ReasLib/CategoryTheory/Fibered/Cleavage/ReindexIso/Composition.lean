/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Functor
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Comparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition comparisons for cleavage reindexing

This leaf owns the canonical comparison between direct reindexing along a composite and
successive reindexing, together with its factorization, naturality, and uniqueness interfaces.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor.Cleavage

variable {p : S ⥤ C} (χ : p.Cleavage)

/-- The ambient-domain comparison underlying the composition reindexing component.

It compares the direct chosen lift over `g ≫ f` with the composite of the chosen lifts over `g`
and `f`, using the canonical strongly-cartesian domain comparison over `Iso.refl W`. -/
noncomputable abbrev Reindex.compAmbientIso
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    ((g ≫ f)⁎[χ] x).1 ≅ (g⁎[χ] (f⁎[χ] x)).1 :=
  IsStronglyCartesian.DomainIso.ofBaseIso (g := Iso.refl W) p
    (Category.id_comp (g ≫ f)).symm
    (χ.cartesianHom g (f⁎[χ] x) ≫ χ.cartesianHom f x)
    (χ.cartesianHom (g ≫ f) x)
    (@IsStronglyCartesian.comp C S _ _ p W V U
      (g⁎[χ] (f⁎[χ] x)).1 (f⁎[χ] x).1 x.1 g f
      (χ.cartesianHom g (f⁎[χ] x)) (χ.cartesianHom f x)
      (χ.reindexLift g (f⁎[χ] x)).isStronglyCartesian
      (χ.reindexLift f x).isStronglyCartesian)
    (χ.reindexLift (g ≫ f) x).isStronglyCartesian

/-- The forward ambient composition comparison lies over `𝟙 W`. -/
theorem Reindex.compAmbientIso.hom.isHomLift
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    p.IsHomLift (𝟙 W) (Reindex.compAmbientIso χ f g x).hom := by
  letI : p.IsStronglyCartesian f (χ.cartesianHom f x) :=
    (χ.reindexLift f x).isStronglyCartesian
  letI : p.IsStronglyCartesian g (χ.cartesianHom g (f⁎[χ] x)) :=
    (χ.reindexLift g (f⁎[χ] x)).isStronglyCartesian
  letI : p.IsStronglyCartesian (g ≫ f) (χ.cartesianHom (g ≫ f) x) :=
    (χ.reindexLift (g ≫ f) x).isStronglyCartesian
  exact IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift p
    (g := Iso.refl W) (Category.id_comp (g ≫ f)).symm
    (χ.cartesianHom g (f⁎[χ] x) ≫ χ.cartesianHom f x)
    (χ.cartesianHom (g ≫ f) x)

/-- The inverse ambient composition comparison lies over `𝟙 W`. -/
theorem Reindex.compAmbientIso.inv.isHomLift
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    p.IsHomLift (𝟙 W) (Reindex.compAmbientIso χ f g x).inv := by
  letI := Reindex.compAmbientIso.hom.isHomLift χ f g x
  exact IsHomLift.lift_id_inv p W (Reindex.compAmbientIso χ f g x)

/-- The component at `x` of the composition comparison
`(g ≫ f)⁎[χ] x ≅ g⁎[χ] (f⁎[χ] x)`. -/
noncomputable def Reindex.compIsoApp
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    (g ≫ f)⁎[χ] x ≅ g⁎[χ] (f⁎[χ] x) :=
  { hom :=
      ⟨(Reindex.compAmbientIso χ f g x).hom,
        Reindex.compAmbientIso.hom.isHomLift χ f g x⟩
    inv :=
      ⟨(Reindex.compAmbientIso χ f g x).inv,
        Reindex.compAmbientIso.inv.isHomLift χ f g x⟩
    hom_inv_id := Fiber.hom_ext (Reindex.compAmbientIso χ f g x).hom_inv_id
    inv_hom_id := Fiber.hom_ext (Reindex.compAmbientIso χ f g x).inv_hom_id }

/-- The forward composition-comparison component factors the iterated cartesian arrow through
the chosen cartesian arrow over the composite. -/
@[reassoc]
theorem Reindex.compIsoApp.hom.fac
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    (Reindex.compIsoApp χ f g x).hom.1 ≫
        χ.cartesianHom g (f⁎[χ] x) ≫ χ.cartesianHom f x =
      χ.cartesianHom (g ≫ f) x := by
  letI : p.IsStronglyCartesian f (χ.cartesianHom f x) :=
    (χ.reindexLift f x).isStronglyCartesian
  letI : p.IsStronglyCartesian g (χ.cartesianHom g (f⁎[χ] x)) :=
    (χ.reindexLift g (f⁎[χ] x)).isStronglyCartesian
  letI : p.IsStronglyCartesian (g ≫ f) (χ.cartesianHom (g ≫ f) x) :=
    (χ.reindexLift (g ≫ f) x).isStronglyCartesian
  change IsStronglyCartesian.map p (g ≫ f)
      (χ.cartesianHom g (f⁎[χ] x) ≫ χ.cartesianHom f x)
      (Category.id_comp (g ≫ f)).symm (χ.cartesianHom (g ≫ f) x) ≫
        (χ.cartesianHom g (f⁎[χ] x) ≫ χ.cartesianHom f x) = _
  exact IsStronglyCartesian.fac p _ _ _ _

/-- The inverse composition-comparison component factors the chosen composite pullback map
through the iterated pullback maps. -/
@[reassoc]
theorem Reindex.compIsoApp.inv.fac
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    (Reindex.compIsoApp χ f g x).inv.1 ≫ χ.cartesianHom (g ≫ f) x =
      χ.cartesianHom g (f⁎[χ] x) ≫ χ.cartesianHom f x := by
  rw [← Reindex.compIsoApp.hom.fac χ f g x]
  change (Reindex.compAmbientIso χ f g x).inv ≫
      (Reindex.compAmbientIso χ f g x).hom ≫
        χ.cartesianHom g (f⁎[χ] x) ≫ χ.cartesianHom f x = _
  simp only [Iso.inv_hom_id_assoc]

/-- Recover the reindexing factorization directly from its mathlib data owner. -/
@[reassoc]
private theorem reindex_map_fac
    {U V : C} (f : V ⟶ U) {x y : Fiber p U} (φ : x ⟶ y) :
    ((f⁎[χ]).map φ).1 ≫ χ.cartesianHom f y = χ.cartesianHom f x ≫ φ.1 := by
  letI : p.IsStronglyCartesian f (χ.cartesianHom f y) :=
    (χ.reindexLift f y).isStronglyCartesian
  letI : p.IsStronglyCartesian f (χ.cartesianHom f x) :=
    (χ.reindexLift f x).isStronglyCartesian
  letI := φ.2
  change IsStronglyCartesian.map p f (χ.cartesianHom f y)
      (Category.id_comp f).symm (χ.cartesianHom f x ≫ φ.1) ≫
        χ.cartesianHom f y = _
  exact IsStronglyCartesian.fac p _ _ _ _

/-- Cancel the iterated cartesian arrow among morphisms in its source fiber. -/
private theorem comp_hom_ext
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U)
    {z : Fiber p W} {φ ψ : z ⟶ g⁎[χ] (f⁎[χ] x)}
    (h : φ.1 ≫ χ.cartesianHom g (f⁎[χ] x) ≫ χ.cartesianHom f x =
      ψ.1 ≫ χ.cartesianHom g (f⁎[χ] x) ≫ χ.cartesianHom f x) : φ = ψ := by
  letI : p.IsStronglyCartesian f (χ.cartesianHom f x) :=
    (χ.reindexLift f x).isStronglyCartesian
  letI : p.IsStronglyCartesian g (χ.cartesianHom g (f⁎[χ] x)) :=
    (χ.reindexLift g (f⁎[χ] x)).isStronglyCartesian
  letI := φ.2
  letI := ψ.2
  apply Fiber.hom_ext
  exact IsCartesian.ext p (g ≫ f)
    (χ.cartesianHom g (f⁎[χ] x) ≫ χ.cartesianHom f x) φ.1 ψ.1 h

/-- Naturality of the componentwise composition comparison. -/
theorem Reindex.compIsoApp.hom.naturality
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {x y : Fiber p U} (φ : x ⟶ y) :
    ((g ≫ f)⁎[χ]).map φ ≫ (Reindex.compIsoApp χ f g y).hom =
      (Reindex.compIsoApp χ f g x).hom ≫
        (f⁎[χ] ⋙ g⁎[χ]).map φ := by
  apply comp_hom_ext χ f g y
  change
    ((((g ≫ f)⁎[χ]).map φ).1 ≫ (Reindex.compIsoApp χ f g y).hom.1) ≫
        χ.cartesianHom g (f⁎[χ] y) ≫ χ.cartesianHom f y =
      ((Reindex.compIsoApp χ f g x).hom.1 ≫
        ((g⁎[χ]).map ((f⁎[χ]).map φ)).1) ≫
        χ.cartesianHom g (f⁎[χ] y) ≫ χ.cartesianHom f y
  simp only [Category.assoc]
  calc
    (((g ≫ f)⁎[χ]).map φ).1 ≫ (Reindex.compIsoApp χ f g y).hom.1 ≫
        χ.cartesianHom g (f⁎[χ] y) ≫ χ.cartesianHom f y =
        (((g ≫ f)⁎[χ]).map φ).1 ≫ χ.cartesianHom (g ≫ f) y :=
      congrArg ((((g ≫ f)⁎[χ]).map φ).1 ≫ ·) (Reindex.compIsoApp.hom.fac χ f g y)
    _ = χ.cartesianHom (g ≫ f) x ≫ φ.1 := reindex_map_fac χ (g ≫ f) φ
    _ = (Reindex.compIsoApp χ f g x).hom.1 ≫ χ.cartesianHom g (f⁎[χ] x) ≫
        χ.cartesianHom f x ≫ φ.1 :=
      (Reindex.compIsoApp.hom.fac_assoc χ f g x φ.1).symm
    _ = (Reindex.compIsoApp χ f g x).hom.1 ≫ χ.cartesianHom g (f⁎[χ] x) ≫
        ((f⁎[χ]).map φ).1 ≫ χ.cartesianHom f y :=
      congrArg (fun k ↦ (Reindex.compIsoApp χ f g x).hom.1 ≫
        χ.cartesianHom g (f⁎[χ] x) ≫ k) (reindex_map_fac χ f φ).symm
    _ = (Reindex.compIsoApp χ f g x).hom.1 ≫ ((g⁎[χ]).map ((f⁎[χ]).map φ)).1 ≫
        χ.cartesianHom g (f⁎[χ] y) ≫ χ.cartesianHom f y :=
      congrArg ((Reindex.compIsoApp χ f g x).hom.1 ≫ ·)
        ((Category.assoc _ _ _).symm.trans
          (reindex_map_fac_assoc χ g ((f⁎[χ]).map φ) (χ.cartesianHom f y)).symm)

/-- Inverse naturality of the componentwise composition comparison. This is the rewrite
orientation used when a morphism has already been reindexed successively. -/
theorem Reindex.compIsoApp.inv.naturality
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {x y : Fiber p U} (φ : x ⟶ y) :
    (f⁎[χ] ⋙ g⁎[χ]).map φ ≫ (Reindex.compIsoApp χ f g y).inv =
      (Reindex.compIsoApp χ f g x).inv ≫
        ((g ≫ f)⁎[χ]).map φ := by
  exact (NatIso.ofComponents (F := (g ≫ f)⁎[χ]) (G := f⁎[χ] ⋙ g⁎[χ])
    (Reindex.compIsoApp χ f g)
    (fun ψ ↦ Reindex.compIsoApp.hom.naturality χ f g ψ)).inv.naturality φ

/-- For composable `f : V ⟶ U` and `g : W ⟶ V`, a cleavage provides the canonical comparison
`(g ≫ f)⁎[χ] ≅ f⁎[χ] ⋙ g⁎[χ]`. -/
@[stacks 02XN, stacks 02XO "(1)"]
noncomputable def Reindex.compIso
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    (g ≫ f)⁎[χ] ≅ f⁎[χ] ⋙ g⁎[χ] :=
  NatIso.ofComponents (Reindex.compIsoApp χ f g)
    (fun φ ↦ Reindex.compIsoApp.hom.naturality χ f g φ)

/-- The forward component of the bundled composition comparison is its named
objectwise comparison. -/
@[simp]
theorem Reindex.compIso.hom.app
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    (Reindex.compIso χ f g).hom.app x = (Reindex.compIsoApp χ f g x).hom := rfl

/-- The inverse component of the bundled composition comparison is its named
objectwise comparison. -/
@[simp]
theorem Reindex.compIso.inv.app
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    (Reindex.compIso χ f g).inv.app x = (Reindex.compIsoApp χ f g x).inv := rfl

/-- The composition comparison is uniquely characterized by its cartesian factorization. -/
theorem Reindex.compIso.unique
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (α : (g ≫ f)⁎[χ] ≅ f⁎[χ] ⋙ g⁎[χ])
    (hα : ∀ x : Fiber p U,
      (α.hom.app x).1 ≫ χ.cartesianHom g (f⁎[χ] x) ≫ χ.cartesianHom f x =
        χ.cartesianHom (g ≫ f) x) :
    α = Reindex.compIso χ f g := by
  apply Iso.ext
  apply NatTrans.ext
  apply funext
  intro x
  apply comp_hom_ext χ f g x
  exact (hα x).trans (Reindex.compIsoApp.hom.fac χ f g x).symm

end Functor.Cleavage

end CategoryTheory
