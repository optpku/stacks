/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Composition

/-!
# Chosen-cleavage reindexing congruence and coherence

This leaf owns comparisons for equal base arrows, specified composites, and
the objectwise pentagon and base-congruence laws for selected reindexing.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor

-- Use the underlying universal properties here, rather than the unproved computation
-- lemmas in the general cleavage API.
private theorem coherence_ext {p : S ⥤ C} {U V : C} {f : V ⟶ U}
    {x y : p.Fiber V} {z : S} {cart : y.1 ⟶ z}
    (hcart : p.IsStronglyCartesian f cart) (φ ψ : x ⟶ y)
    (h : φ.1 ≫ cart = ψ.1 ≫ cart) : φ = ψ := by
  apply Fiber.hom_ext
  exact @IsStronglyCartesian.ext C S _ _ p V U y.1 z f cart hcart V x.1
    (𝟙 V) φ.1 ψ.1 φ.2 ψ.2 h

@[reassoc]
private theorem coherence_map_fac {p : S ⥤ C} (χ : p.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    ((χ.reindex f).map φ).1 ≫ χ.cartesianHom f y =
      χ.cartesianHom f x ≫ φ.1 := by
  letI : p.IsStronglyCartesian f (χ.cartesianHom f y) :=
    (χ.reindexLift f y).isStronglyCartesian
  letI : p.IsHomLift f (χ.cartesianHom f x ≫ φ.1) :=
    @IsHomLift.comp_lift_id_right' C S _ _ p V U
      (χ.reindexObj f x).1 x.1 y.1 f (χ.cartesianHom f x)
      (χ.reindexLift f x).isStronglyCartesian.toIsHomLift U φ.1 φ.2
  exact IsStronglyCartesian.fac p f (χ.cartesianHom f y)
    (Category.id_comp f).symm (χ.cartesianHom f x ≫ φ.1)

@[reassoc]
private theorem coherence_comp_fac {p : S ⥤ C} (χ : p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U) :
    (Cleavage.Reindex.compIsoApp χ f g x).hom.1 ≫
        χ.cartesianHom g (χ.reindexObj f x) ≫ χ.cartesianHom f x =
      χ.cartesianHom (g ≫ f) x := by
  letI : p.IsStronglyCartesian f (χ.cartesianHom f x) :=
    (χ.reindexLift f x).isStronglyCartesian
  letI : p.IsStronglyCartesian g (χ.cartesianHom g (χ.reindexObj f x)) :=
    (χ.reindexLift g (χ.reindexObj f x)).isStronglyCartesian
  letI : p.IsHomLift (g ≫ f) (χ.cartesianHom (g ≫ f) x) :=
    (χ.reindexLift (g ≫ f) x).isStronglyCartesian.toIsHomLift
  dsimp only [Cleavage.Reindex.compIsoApp, Cleavage.Reindex.compAmbientIso,
    IsStronglyCartesian.DomainIso.ofBaseIso, IsStronglyCartesian.domainIsoOfBaseIso]
  apply IsStronglyCartesian.fac

@[reassoc]
private theorem coherence_specified_fac {p : S ⥤ C} (χ : p.Cleavage)
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) (x : p.Fiber D) :
    (Cleavage.Reindex.specifiedCompIsoApp χ f g gf hgf x).hom.1 ≫
        χ.cartesianHom g (χ.reindexObj f x) ≫ χ.cartesianHom f x =
      χ.cartesianHom gf x := by
  subst gf
  simp only [Cleavage.Reindex.specifiedCompIsoApp, Cleavage.Reindex.congrIsoApp,
    eqToIso_refl, Iso.trans_hom, Iso.refl_hom, Category.id_comp]
  exact coherence_comp_fac χ f g x

private theorem coherence_comp_ext {p : S ⥤ C} (χ : p.Cleavage)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) {x : p.Fiber U} {y : p.Fiber W}
    (φ ψ : y ⟶ (χ.reindex g).obj ((χ.reindex f).obj x))
    (h : φ.1 ≫ χ.cartesianHom g (χ.reindexObj f x) ≫ χ.cartesianHom f x =
      ψ.1 ≫ χ.cartesianHom g (χ.reindexObj f x) ≫ χ.cartesianHom f x) : φ = ψ := by
  apply coherence_ext
    (@IsStronglyCartesian.comp C S _ _ p W V U
      (χ.reindexObj g (χ.reindexObj f x)).1 (χ.reindexObj f x).1 x.1 g f
      (χ.cartesianHom g (χ.reindexObj f x)) (χ.cartesianHom f x)
      (χ.reindexLift g (χ.reindexObj f x)).isStronglyCartesian
      (χ.reindexLift f x).isStronglyCartesian) φ ψ
  exact h

private theorem coherence_id_fac {p : S ⥤ C} (χ : p.Cleavage)
    (U : C) (x : p.Fiber U) :
    (Cleavage.Reindex.idIsoApp χ U x).hom.1 ≫ χ.cartesianHom (𝟙 U) x = 𝟙 x.1 := by
  letI : p.IsStronglyCartesian (𝟙 U) (χ.cartesianHom (𝟙 U) x) :=
    (χ.reindexLift (𝟙 U) x).isStronglyCartesian
  letI : p.IsHomLift (𝟙 U) (𝟙 x.1) := (𝟙 x : x ⟶ x).2
  dsimp only [Cleavage.Reindex.idIsoApp, Cleavage.Reindex.idAmbientIso,
    IsStronglyCartesian.DomainIso.ofBaseIso, IsStronglyCartesian.domainIsoOfBaseIso]
  apply IsStronglyCartesian.fac

private theorem coherence_eqId_hom {p : S ⥤ C} (χ : p.Cleavage)
    {U : C} (f : U ⟶ U) (hf : f = 𝟙 U) (x : p.Fiber U) :
    (Cleavage.Reindex.eqId.isoApp χ f hf x).hom.1 = χ.cartesianHom f x := by
  subst f
  have hi := (Fiber.fiberInclusion.mapIso
    (Cleavage.Reindex.idIsoApp χ U x)).hom_comp_eq_id.mp (coherence_id_fac χ U x)
  simp only [Cleavage.Reindex.eqId.isoApp, Cleavage.Reindex.congrIsoApp,
    eqToIso_refl, Iso.trans_hom, Iso.refl_hom, Iso.symm_hom, Category.id_comp]
  exact hi.symm

@[reassoc]
private theorem coherence_vertical_fac {p : S ⥤ C} (χ : p.Cleavage)
    {x y : S} (φ : x ⟶ y) :
    (χ.verticalFactor φ).1 ≫ χ.cartesianHom (p.map φ) (Fiber.mk rfl) = φ := by
  exact @IsStronglyCartesian.fac C S _ _ p (p.obj x) (p.obj y)
    (χ.reindexObj (p.map φ) (Fiber.mk rfl)).1 y (p.map φ)
    (χ.cartesianHom (p.map φ) (Fiber.mk rfl))
    (χ.reindexLift (p.map φ) (Fiber.mk rfl)).isStronglyCartesian
    (p.obj x) x (𝟙 (p.obj x)) (𝟙 (p.obj x) ≫ p.map φ) rfl φ
    (IsHomLift.lift_id_comp p (p.map φ) φ)

/-- The selected objectwise comparison between reindexing along equal base arrows. -/
noncomputable def Chosen.Reindex.congrIsoApp (p : S ⥤ C) [p.IsFibered]
    {U V : C} {f g : V ⟶ U} (h : f = g) (x : p.Fiber U) :
    (Chosen.reindex p f).obj x ≅ (Chosen.reindex p g).obj x :=
  Cleavage.Reindex.congrIsoApp (Cleavage.ofIsFibered p) h x

/-- The selected objectwise comparison along equal base arrows is natural in the fiber
object. -/
theorem Chosen.Reindex.congrIsoApp.hom.naturality (p : S ⥤ C) [p.IsFibered]
    {U V : C} {f g : V ⟶ U} (h : f = g)
    {x y : p.Fiber U} (φ : x ⟶ y) :
    (Chosen.reindex p f).map φ ≫
        (Chosen.Reindex.congrIsoApp p h y).hom =
      (Chosen.Reindex.congrIsoApp p h x).hom ≫
        (Chosen.reindex p g).map φ := by
  cases h
  simp only [Chosen.reindex, Chosen.Reindex.congrIsoApp, Cleavage.Reindex.congrIsoApp,
    eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- The inverse selected comparison along equal base arrows is natural in the fiber object. -/
theorem Chosen.Reindex.congrIsoApp.inv.naturality (p : S ⥤ C) [p.IsFibered]
    {U V : C} {f g : V ⟶ U} (h : f = g)
    {x y : p.Fiber U} (φ : x ⟶ y) :
    (Chosen.reindex p g).map φ ≫
        (Chosen.Reindex.congrIsoApp p h y).inv =
      (Chosen.Reindex.congrIsoApp p h x).inv ≫
        (Chosen.reindex p f).map φ := by
  cases h
  simp only [Chosen.reindex, Chosen.Reindex.congrIsoApp, Cleavage.Reindex.congrIsoApp,
    eqToIso_refl, Iso.refl_inv, Category.comp_id, Category.id_comp]

/-- Equal base arrows induce naturally isomorphic selected reindexing functors. -/
noncomputable def Chosen.Reindex.congrIso (p : S ⥤ C) [p.IsFibered]
    {U V : C} {f g : V ⟶ U} (h : f = g) :
    Chosen.reindex p f ≅ Chosen.reindex p g :=
  Cleavage.Reindex.congrIso (Cleavage.ofIsFibered p) h

/-- The forward selected comparison along equal base arrows carries the selected cartesian arrow
over `g` to the selected cartesian arrow over `f`. -/
@[reassoc]
theorem Chosen.Reindex.congrIsoApp.hom.fac
    (p : S ⥤ C) [p.IsFibered]
    {U V : C} {f g : V ⟶ U} (h : f = g) (x : p.Fiber U) :
    (Chosen.Reindex.congrIsoApp p h x).hom.1 ≫ Chosen.cartesianHom p g x =
      Chosen.cartesianHom p f x := by
  cases h
  change 𝟙 _ ≫ Chosen.cartesianHom p f x = _
  exact Category.id_comp _

/-- The inverse selected comparison along equal base arrows carries the selected cartesian arrow
over `f` to the selected cartesian arrow over `g`. -/
@[reassoc]
theorem Chosen.Reindex.congrIsoApp.inv.fac
    (p : S ⥤ C) [p.IsFibered]
    {U V : C} {f g : V ⟶ U} (h : f = g) (x : p.Fiber U) :
    (Chosen.Reindex.congrIsoApp p h x).inv.1 ≫ Chosen.cartesianHom p f x =
      Chosen.cartesianHom p g x := by
  cases h
  change 𝟙 _ ≫ Chosen.cartesianHom p f x = _
  exact Category.id_comp _

/-- Reindexing along an endomorphism identified with the identity is canonically isomorphic to
the identity action on the fiber. -/
noncomputable def Chosen.Reindex.eqId.isoApp (p : S ⥤ C) [p.IsFibered]
    {U : C} (f : U ⟶ U) (hf : f = 𝟙 U) (x : p.Fiber U) :
    (Chosen.reindex p f).obj x ≅ x :=
  Cleavage.Reindex.eqId.isoApp (Cleavage.ofIsFibered p) f hf x

/-- The canonical comparison from reindexing along an arrow equal to the identity is natural in
the fiber object. -/
theorem Chosen.Reindex.eqId.isoApp.hom.naturality
    (p : S ⥤ C) [p.IsFibered]
    {U : C} (f : U ⟶ U) (hf : f = 𝟙 U)
    {x y : p.Fiber U} (φ : x ⟶ y) :
    (Chosen.reindex p f).map φ ≫ (Chosen.Reindex.eqId.isoApp p f hf y).hom =
      (Chosen.Reindex.eqId.isoApp p f hf x).hom ≫ φ := by
  apply Fiber.hom_ext
  change ((Chosen.reindex p f).map φ).1 ≫
      (Chosen.Reindex.eqId.isoApp p f hf y).hom.1 =
    (Chosen.Reindex.eqId.isoApp p f hf x).hom.1 ≫ φ.1
  erw [coherence_eqId_hom, coherence_eqId_hom]
  exact coherence_map_fac (Cleavage.ofIsFibered p) f φ

/-- The underlying arrow of the identity-specialized reindexing comparison is the selected
cartesian arrow. -/
theorem Chosen.Reindex.eqId.isoApp.hom.eq_cartesianHom
    (p : S ⥤ C) [p.IsFibered]
    {U : C} (f : U ⟶ U) (hf : f = 𝟙 U) (x : p.Fiber U) :
    (Chosen.Reindex.eqId.isoApp p f hf x).hom.1 = Chosen.cartesianHom p f x := by
  exact coherence_eqId_hom (Cleavage.ofIsFibered p) f hf x

/-- Reindexing along an endomorphism equal to the identity is naturally isomorphic to the
identity functor of the fiber. -/
noncomputable def Chosen.Reindex.eqId.iso (p : S ⥤ C) [p.IsFibered]
    {U : C} (f : U ⟶ U) (hf : f = 𝟙 U) :
    Chosen.reindex p f ≅ 𝟭 (p.Fiber U) :=
  Cleavage.Reindex.eqId.iso (Cleavage.ofIsFibered p) f hf

/-- If `q` is identified with an identity, this is the canonical comparison from direct
reindexing along `f` to reindexing first along `q` and then along `f`. -/
noncomputable def Chosen.Reindex.eqId.compIsoApp
    (p : S ⥤ C) [p.IsFibered]
    {U V : C} (q : U ⟶ U) (hq : q = 𝟙 U) (f : V ⟶ U) (x : p.Fiber U) :
    (Chosen.reindex p f).obj x ≅
      (Chosen.reindex p f).obj ((Chosen.reindex p q).obj x) :=
  Cleavage.Reindex.eqId.compIsoApp (Cleavage.ofIsFibered p) q hq f x

/-- The composition comparison with an identity-like first arrow cancels the corresponding
identity-specialized reindexing comparison. -/
theorem Chosen.Reindex.eqId.compIsoApp.hom.cancellation
    (p : S ⥤ C) [p.IsFibered]
    {U V : C} (q : U ⟶ U) (hq : q = 𝟙 U) (f : V ⟶ U) (x : p.Fiber U) :
    (Chosen.Reindex.eqId.compIsoApp p q hq f x).hom ≫
        (Chosen.reindex p f).map (Chosen.Reindex.eqId.isoApp p q hq x).hom =
      𝟙 ((Chosen.reindex p f).obj x) := by
  let χ := Cleavage.ofIsFibered p
  apply coherence_ext (χ.reindexLift f x).isStronglyCartesian
  change ((Chosen.Reindex.eqId.compIsoApp p q hq f x).hom.1 ≫
      ((Chosen.reindex p f).map (Chosen.Reindex.eqId.isoApp p q hq x).hom).1) ≫
        χ.cartesianHom f x = 𝟙 _ ≫ χ.cartesianHom f x
  erw [Category.assoc, coherence_map_fac, coherence_eqId_hom, Category.id_comp]
  exact coherence_specified_fac χ q f f
    ((congrArg (fun e ↦ f ≫ e) hq).trans (Category.comp_id f)) x

/-- Inverse form of the cancellation between composition with an identity-like arrow and its
identity-specialized reindexing comparison. -/
theorem Chosen.Reindex.eqId.compIsoApp.inv.cancellation
    (p : S ⥤ C) [p.IsFibered]
    {U V : C} (q : U ⟶ U) (hq : q = 𝟙 U) (f : V ⟶ U) (x : p.Fiber U) :
    (Chosen.Reindex.eqId.compIsoApp p q hq f x).inv =
      (Chosen.reindex p f).map (Chosen.Reindex.eqId.isoApp p q hq x).hom := by
  symm
  exact (Chosen.Reindex.eqId.compIsoApp p q hq f x).hom_comp_eq_id.mp
    (Chosen.Reindex.eqId.compIsoApp.hom.cancellation p q hq f x)

/-- The selected objectwise composition comparison for a specified composite `gf`. -/
noncomputable def Chosen.Reindex.specifiedCompIsoApp
    (p : S ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) (x : p.Fiber D) :
    Chosen.reindexObj p gf x ≅
      Chosen.reindexObj p g (Chosen.reindexObj p f x) :=
  Cleavage.Reindex.specifiedCompIsoApp (Cleavage.ofIsFibered p) f g gf hgf x

/-- The forward selected comparison over a specified composite factors the iterated selected
cartesian arrows through the selected arrow over `gf`. -/
@[reassoc]
theorem Chosen.Reindex.specifiedCompIsoApp.hom.fac
    (p : S ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) (x : p.Fiber D) :
    (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf x).hom.1 ≫
        Chosen.cartesianHom p g (Chosen.reindexObj p f x) ≫
        Chosen.cartesianHom p f x =
      Chosen.cartesianHom p gf x := by
  subst gf
  simp only [Chosen.Reindex.specifiedCompIsoApp, Cleavage.Reindex.specifiedCompIsoApp,
    Cleavage.Reindex.congrIsoApp, eqToIso_refl, Iso.trans_hom, Iso.refl_hom,
    Category.id_comp]
  exact coherence_comp_fac (Cleavage.ofIsFibered p) f g x

/-- The inverse selected comparison over a specified composite factors the selected arrow over
`gf` through the two iterated selected cartesian arrows. -/
@[reassoc]
theorem Chosen.Reindex.specifiedCompIsoApp.inv.fac
    (p : S ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) (x : p.Fiber D) :
    (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf x).inv.1 ≫
        Chosen.cartesianHom p gf x =
      Chosen.cartesianHom p g (Chosen.reindexObj p f x) ≫
        Chosen.cartesianHom p f x := by
  apply (Fiber.fiberInclusion.mapIso
    (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf x)).inv_comp_eq.mpr
  exact (Chosen.Reindex.specifiedCompIsoApp.hom.fac p f g gf hgf x).symm

/-- Naturality of the forward selected comparison over a specified composite. -/
theorem Chosen.Reindex.specifiedCompIsoApp.hom.naturality
    (p : S ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) {x y : p.Fiber D} (φ : x ⟶ y) :
    Chosen.reindexMap p gf φ ≫
        (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf y).hom =
      (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf x).hom ≫
        Chosen.reindexMap p g (Chosen.reindexMap p f φ) := by
  let χ := Cleavage.ofIsFibered p
  apply coherence_comp_ext χ f g
  change ((Chosen.reindexMap p gf φ).1 ≫
      (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf y).hom.1) ≫
        χ.cartesianHom g (χ.reindexObj f y) ≫ χ.cartesianHom f y =
    ((Chosen.Reindex.specifiedCompIsoApp p f g gf hgf x).hom.1 ≫
      (Chosen.reindexMap p g (Chosen.reindexMap p f φ)).1) ≫
        χ.cartesianHom g (χ.reindexObj f y) ≫ χ.cartesianHom f y
  simp only [Chosen.reindexMap, Chosen.Reindex.specifiedCompIsoApp, Category.assoc]
  erw [coherence_specified_fac χ f g gf hgf y, coherence_map_fac χ gf φ,
    coherence_map_fac_assoc χ g ((χ.reindex f).map φ),
    Category.assoc (χ.cartesianHom g ((χ.reindex f).obj x))
      ((χ.reindex f).map φ).1 (χ.cartesianHom f y),
    coherence_map_fac χ f φ, coherence_specified_fac_assoc χ f g gf hgf x]
  rfl

/-- Naturality of the inverse selected comparison over a specified composite. -/
theorem Chosen.Reindex.specifiedCompIsoApp.inv.naturality
    (p : S ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) {x y : p.Fiber D} (φ : x ⟶ y) :
    Chosen.reindexMap p g (Chosen.reindexMap p f φ) ≫
        (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf y).inv =
      (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf x).inv ≫
        Chosen.reindexMap p gf φ := by
  apply (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf y).comp_inv_eq.mpr
  rw [Category.assoc, Chosen.Reindex.specifiedCompIsoApp.hom.naturality]
  simp

/-- Conjugating direct selected reindexing along a specified composite gives successive selected
reindexing. -/
@[reassoc]
theorem Chosen.Reindex.specifiedCompIsoApp.conjugation.toIterated
    (p : S ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) {x y : p.Fiber D} (φ : x ⟶ y) :
    (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf x).inv ≫
        Chosen.reindexMap p gf φ ≫
        (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf y).hom =
      Chosen.reindexMap p g (Chosen.reindexMap p f φ) := by
  rw [Chosen.Reindex.specifiedCompIsoApp.hom.naturality]
  simp

/-- Conjugating successive selected reindexing by the specified-composite comparison recovers
direct selected reindexing. -/
@[reassoc]
theorem Chosen.Reindex.specifiedCompIsoApp.conjugation.toComposite
    (p : S ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) {x y : p.Fiber D} (φ : x ⟶ y) :
    (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf x).hom ≫
        Chosen.reindexMap p g (Chosen.reindexMap p f φ) ≫
        (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf y).inv =
      Chosen.reindexMap p gf φ := by
  rw [Chosen.Reindex.specifiedCompIsoApp.inv.naturality]
  simp

/-- A specified composite induces a natural selected composition comparison. -/
noncomputable def Chosen.Reindex.specifiedCompIso
    (p : S ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) :
    Chosen.reindex p gf ≅ Chosen.reindex p f ⋙ Chosen.reindex p g :=
  Cleavage.Reindex.specifiedCompIso (Cleavage.ofIsFibered p) f g gf hgf

/-- Pulling a selected composition comparison back along a third arrow satisfies the objectwise
pentagon, with the associativity transport displayed explicitly. -/
theorem Chosen.Reindex.compIsoApp.pentagon.hom (p : S ⥤ C) [p.IsFibered]
    {T V W Z : C} (f : V ⟶ T) (g : W ⟶ V) (h : Z ⟶ W)
    (x : p.Fiber T) :
    (Chosen.reindex p h).map ((Chosen.Reindex.compIsoApp p f g x).hom) =
      (Chosen.Reindex.compIsoApp p (g ≫ f) h x).inv ≫
        eqToHom
          (congrArg (fun r ↦ (Chosen.reindex p r).obj x)
            (Category.assoc h g f).symm) ≫
        (Chosen.Reindex.compIsoApp p f (h ≫ g) x).hom ≫
        (Chosen.Reindex.compIsoApp p g h ((Chosen.reindex p f).obj x)).hom := by
  let χ := Cleavage.ofIsFibered p
  apply (Chosen.Reindex.compIsoApp p (g ≫ f) h x).eq_inv_comp.mpr
  letI : p.IsStronglyCartesian f (χ.cartesianHom f x) :=
    (χ.reindexLift f x).isStronglyCartesian
  letI : p.IsStronglyCartesian g (χ.cartesianHom g (χ.reindexObj f x)) :=
    (χ.reindexLift g (χ.reindexObj f x)).isStronglyCartesian
  letI : p.IsStronglyCartesian h
      (χ.cartesianHom h (χ.reindexObj g (χ.reindexObj f x))) :=
    (χ.reindexLift h (χ.reindexObj g (χ.reindexObj f x))).isStronglyCartesian
  apply coherence_ext (inferInstance : p.IsStronglyCartesian (h ≫ g ≫ f)
    (χ.cartesianHom h (χ.reindexObj g (χ.reindexObj f x)) ≫
      χ.cartesianHom g (χ.reindexObj f x) ≫ χ.cartesianHom f x))
  change ((Cleavage.Reindex.compIsoApp χ (g ≫ f) h x).hom.1 ≫
      ((χ.reindex h).map (Cleavage.Reindex.compIsoApp χ f g x).hom).1) ≫
        χ.cartesianHom h (χ.reindexObj g (χ.reindexObj f x)) ≫
        χ.cartesianHom g (χ.reindexObj f x) ≫ χ.cartesianHom f x =
    ((eqToHom (congrArg (fun r ↦ χ.reindexObj r x)
        (Category.assoc h g f).symm)).1 ≫
      (Cleavage.Reindex.compIsoApp χ f (h ≫ g) x).hom.1 ≫
      (Cleavage.Reindex.compIsoApp χ g h (χ.reindexObj f x)).hom.1) ≫
        χ.cartesianHom h (χ.reindexObj g (χ.reindexObj f x)) ≫
        χ.cartesianHom g (χ.reindexObj f x) ≫ χ.cartesianHom f x
  set_option backward.isDefEq.respectTransparency false in
    simp only [Category.assoc, coherence_map_fac_assoc,
      coherence_comp_fac, coherence_comp_fac_assoc]
  exact (Chosen.Reindex.congrIsoApp.hom.fac p (Category.assoc h g f).symm x).symm

/-- Inverse form of the objectwise pentagon for selected reindexing. -/
theorem Chosen.Reindex.compIsoApp.pentagon.inv (p : S ⥤ C) [p.IsFibered]
    {T V W Z : C} (f : V ⟶ T) (g : W ⟶ V) (h : Z ⟶ W)
    (x : p.Fiber T) :
    (Chosen.reindex p h).map ((Chosen.Reindex.compIsoApp p f g x).inv) =
      (Chosen.Reindex.compIsoApp p g h ((Chosen.reindex p f).obj x)).inv ≫
        (Chosen.Reindex.compIsoApp p f (h ≫ g) x).inv ≫
        eqToHom
          (congrArg (fun r ↦ (Chosen.reindex p r).obj x)
            (Category.assoc h g f)) ≫
        (Chosen.Reindex.compIsoApp p (g ≫ f) h x).hom := by
  have he : (Chosen.reindex p h).mapIso (Chosen.Reindex.compIsoApp p f g x) =
      (Chosen.Reindex.compIsoApp p (g ≫ f) h x).symm ≪≫
        eqToIso (congrArg (fun r ↦ (Chosen.reindex p r).obj x)
          (Category.assoc h g f).symm) ≪≫
        Chosen.Reindex.compIsoApp p f (h ≫ g) x ≪≫
        Chosen.Reindex.compIsoApp p g h ((Chosen.reindex p f).obj x) := by
    apply Iso.ext
    exact Chosen.Reindex.compIsoApp.pentagon.hom p f g h x
  have hi := congrArg Iso.inv he
  simpa only [Functor.mapIso_inv, Iso.trans_inv, Iso.symm_inv, eqToIso.inv,
    Category.assoc] using hi

/-- The forward selected composition comparison is natural under equality of its second base
arrow, with both dependent transports exposed. -/
theorem Chosen.Reindex.compIsoApp.baseCongr.hom (p : S ⥤ C) [p.IsFibered]
    {T V W : C} (f : V ⟶ T) {g g' : W ⟶ V} (h : g = g')
    (x : p.Fiber T) :
    (Chosen.Reindex.compIsoApp p f g x).hom ≫
        eqToHom
          (congrArg (fun r ↦ (Chosen.reindex p r).obj
            ((Chosen.reindex p f).obj x)) h) =
      eqToHom
          (congrArg (fun r ↦ (Chosen.reindex p r).obj x)
            (congrArg (fun r ↦ r ≫ f) h)) ≫
        (Chosen.Reindex.compIsoApp p f g' x).hom := by
  cases h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- The inverse selected composition comparison is natural under equality of its second base
arrow. -/
theorem Chosen.Reindex.compIsoApp.baseCongr.inv (p : S ⥤ C) [p.IsFibered]
    {T V W : C} (f : V ⟶ T) {g g' : W ⟶ V} (h : g = g')
    (x : p.Fiber T) :
    (Chosen.Reindex.compIsoApp p f g' x).inv ≫
        eqToHom
          (congrArg (fun r ↦ (Chosen.reindex p r).obj x)
            (congrArg (fun r ↦ r ≫ f) h)).symm =
      eqToHom
          (congrArg (fun r ↦ (Chosen.reindex p r).obj
            ((Chosen.reindex p f).obj x)) h).symm ≫
        (Chosen.Reindex.compIsoApp p f g x).inv := by
  cases h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- The selected vertical factor of an identity is the inverse identity-reindexing comparison. -/
theorem Chosen.verticalFactor.id (p : S ⥤ C) [p.IsFibered] (x : S) :
    Chosen.verticalFactor p (𝟙 x) =
      (Chosen.Reindex.eqId.isoApp p (p.map (𝟙 x)) (p.map_id x)
        (Fiber.mk (p := p) (a := x) rfl : p.Fiber (p.obj x))).inv := by
  let χ := Cleavage.ofIsFibered p
  apply coherence_ext
    (χ.reindexLift (p.map (𝟙 x)) (Fiber.mk rfl)).isStronglyCartesian
  change (χ.verticalFactor (𝟙 x)).1 ≫ χ.cartesianHom (p.map (𝟙 x)) (Fiber.mk rfl) =
    (Chosen.Reindex.eqId.isoApp p (p.map (𝟙 x)) (p.map_id x) (Fiber.mk rfl)).inv.1 ≫
      χ.cartesianHom (p.map (𝟙 x)) (Fiber.mk rfl)
  rw [coherence_vertical_fac]
  erw [← coherence_eqId_hom χ (p.map (𝟙 x)) (p.map_id x) (Fiber.mk rfl)]
  exact (Fiber.fiberInclusion.mapIso
    (Chosen.Reindex.eqId.isoApp p (p.map (𝟙 x)) (p.map_id x) (Fiber.mk rfl))).inv_hom_id.symm

/-- The selected vertical factor of a composite is obtained by composing the first vertical
factor with the reindexing of the second and the inverse selected composition comparison. -/
theorem Chosen.verticalFactor.comp (p : S ⥤ C) [p.IsFibered]
    {x y z : S} (φ : x ⟶ y) (ψ : y ⟶ z) :
    Chosen.verticalFactor p (φ ≫ ψ) =
      Chosen.verticalFactor p φ ≫
        (Chosen.reindex p (p.map φ)).map (Chosen.verticalFactor p ψ) ≫
        (Chosen.Reindex.specifiedCompIsoApp p
          (p.map ψ) (p.map φ) (p.map (φ ≫ ψ))
          (p.map_comp φ ψ).symm
          (Fiber.mk (p := p) (a := z) rfl : p.Fiber (p.obj z))).inv := by
  let χ := Cleavage.ofIsFibered p
  apply coherence_ext
    (χ.reindexLift (p.map (φ ≫ ψ)) (Fiber.mk rfl)).isStronglyCartesian
  change (χ.verticalFactor (φ ≫ ψ)).1 ≫
      χ.cartesianHom (p.map (φ ≫ ψ)) (Fiber.mk rfl) =
    ((χ.verticalFactor φ).1 ≫
      ((χ.reindex (p.map φ)).map (χ.verticalFactor ψ)).1 ≫
      (Chosen.Reindex.specifiedCompIsoApp p (p.map ψ) (p.map φ) (p.map (φ ≫ ψ))
        (p.map_comp φ ψ).symm (Fiber.mk rfl)).inv.1) ≫
      χ.cartesianHom (p.map (φ ≫ ψ)) (Fiber.mk rfl)
  simp only [Category.assoc]
  erw [Chosen.Reindex.specifiedCompIsoApp.inv.fac]
  erw [coherence_vertical_fac χ (φ ≫ ψ),
    coherence_map_fac_assoc χ (p.map φ) (χ.verticalFactor ψ), Category.assoc,
    coherence_vertical_fac χ ψ, coherence_vertical_fac_assoc χ φ]
  rfl

end Functor

end CategoryTheory
