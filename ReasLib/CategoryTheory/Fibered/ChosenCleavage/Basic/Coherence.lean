/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
        (Chosen.reindex p g).map φ := sorry

/-- The inverse selected comparison along equal base arrows is natural in the fiber object. -/
theorem Chosen.Reindex.congrIsoApp.inv.naturality (p : S ⥤ C) [p.IsFibered]
    {U V : C} {f g : V ⟶ U} (h : f = g)
    {x y : p.Fiber U} (φ : x ⟶ y) :
    (Chosen.reindex p g).map φ ≫
        (Chosen.Reindex.congrIsoApp p h y).inv =
      (Chosen.Reindex.congrIsoApp p h x).inv ≫
        (Chosen.reindex p f).map φ := sorry

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
      Chosen.cartesianHom p f x := sorry

/-- The inverse selected comparison along equal base arrows carries the selected cartesian arrow
over `f` to the selected cartesian arrow over `g`. -/
@[reassoc]
theorem Chosen.Reindex.congrIsoApp.inv.fac
    (p : S ⥤ C) [p.IsFibered]
    {U V : C} {f g : V ⟶ U} (h : f = g) (x : p.Fiber U) :
    (Chosen.Reindex.congrIsoApp p h x).inv.1 ≫ Chosen.cartesianHom p f x =
      Chosen.cartesianHom p g x := sorry

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
      (Chosen.Reindex.eqId.isoApp p f hf x).hom ≫ φ := sorry

/-- The underlying arrow of the identity-specialized reindexing comparison is the selected
cartesian arrow. -/
theorem Chosen.Reindex.eqId.isoApp.hom.eq_cartesianHom
    (p : S ⥤ C) [p.IsFibered]
    {U : C} (f : U ⟶ U) (hf : f = 𝟙 U) (x : p.Fiber U) :
    (Chosen.Reindex.eqId.isoApp p f hf x).hom.1 = Chosen.cartesianHom p f x := sorry

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
      𝟙 ((Chosen.reindex p f).obj x) := sorry

/-- Inverse form of the cancellation between composition with an identity-like arrow and its
identity-specialized reindexing comparison. -/
theorem Chosen.Reindex.eqId.compIsoApp.inv.cancellation
    (p : S ⥤ C) [p.IsFibered]
    {U V : C} (q : U ⟶ U) (hq : q = 𝟙 U) (f : V ⟶ U) (x : p.Fiber U) :
    (Chosen.Reindex.eqId.compIsoApp p q hq f x).inv =
      (Chosen.reindex p f).map (Chosen.Reindex.eqId.isoApp p q hq x).hom := sorry

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
      Chosen.cartesianHom p gf x := sorry

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
        Chosen.cartesianHom p f x := sorry

/-- Naturality of the forward selected comparison over a specified composite. -/
theorem Chosen.Reindex.specifiedCompIsoApp.hom.naturality
    (p : S ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) {x y : p.Fiber D} (φ : x ⟶ y) :
    Chosen.reindexMap p gf φ ≫
        (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf y).hom =
      (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf x).hom ≫
        Chosen.reindexMap p g (Chosen.reindexMap p f φ) := sorry

/-- Naturality of the inverse selected comparison over a specified composite. -/
theorem Chosen.Reindex.specifiedCompIsoApp.inv.naturality
    (p : S ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) {x y : p.Fiber D} (φ : x ⟶ y) :
    Chosen.reindexMap p g (Chosen.reindexMap p f φ) ≫
        (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf y).inv =
      (Chosen.Reindex.specifiedCompIsoApp p f g gf hgf x).inv ≫
        Chosen.reindexMap p gf φ := sorry

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
      Chosen.reindexMap p g (Chosen.reindexMap p f φ) := sorry

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
      Chosen.reindexMap p gf φ := sorry

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
        (Chosen.Reindex.compIsoApp p g h ((Chosen.reindex p f).obj x)).hom := sorry

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
        (Chosen.Reindex.compIsoApp p (g ≫ f) h x).hom := sorry

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
        (Chosen.Reindex.compIsoApp p f g' x).hom := sorry

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
        (Chosen.Reindex.compIsoApp p f g x).inv := sorry

/-- The selected vertical factor of an identity is the inverse identity-reindexing comparison. -/
theorem Chosen.verticalFactor.id (p : S ⥤ C) [p.IsFibered] (x : S) :
    Chosen.verticalFactor p (𝟙 x) =
      (Chosen.Reindex.eqId.isoApp p (p.map (𝟙 x)) (p.map_id x)
        (Fiber.mk (p := p) (a := x) rfl : p.Fiber (p.obj x))).inv := sorry

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
          (Fiber.mk (p := p) (a := z) rfl : p.Fiber (p.obj z))).inv := sorry

end Functor

end CategoryTheory
