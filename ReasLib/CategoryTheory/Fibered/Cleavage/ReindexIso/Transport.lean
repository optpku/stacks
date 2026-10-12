/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Composition

/-!
# Base-arrow transport and specified-composite comparisons

This leaf exposes reindexing along equal base arrows as a named natural isomorphism and builds
comparison maps over a specified composite without forcing downstream code to manage raw
dependent transports.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor.Cleavage

variable {p : S ⥤ C} (χ : p.Cleavage)

/-- The canonical objectwise comparison between reindexing along equal base arrows. This names
the dependent transport that otherwise appears downstream as a raw `eqToIso`. -/
noncomputable def Reindex.congrIsoApp
    {U V : C} {f g : V ⟶ U} (h : f = g) (x : Fiber p U) :
    (χ.reindex f).obj x ≅ (χ.reindex g).obj x :=
  eqToIso (congrArg (fun r ↦ χ.reindexObj r x) h)

/-- Reindexing transport along an equality of base arrows is natural in the fiber object. -/
theorem Reindex.congrIsoApp.hom.naturality
    {U V : C} {f g : V ⟶ U} (h : f = g)
    {x y : Fiber p U} (φ : x ⟶ y) :
    (χ.reindex f).map φ ≫ (Reindex.congrIsoApp χ h y).hom =
      (Reindex.congrIsoApp χ h x).hom ≫
        (χ.reindex g).map φ := sorry

/-- Inverse naturality of reindexing transport along an equality of base arrows. -/
theorem Reindex.congrIsoApp.inv.naturality
    {U V : C} {f g : V ⟶ U} (h : f = g)
    {x y : Fiber p U} (φ : x ⟶ y) :
    (χ.reindex g).map φ ≫ (Reindex.congrIsoApp χ h y).inv =
      (Reindex.congrIsoApp χ h x).inv ≫
        (χ.reindex f).map φ := sorry

/-- Equal base arrows induce naturally isomorphic reindexing functors. -/
@[stacks 02XN]
noncomputable def Reindex.congrIso
    {U V : C} {f g : V ⟶ U} (h : f = g) :
    χ.reindex f ≅ χ.reindex g :=
  NatIso.ofComponents (Reindex.congrIsoApp χ h)
    (fun φ ↦ Reindex.congrIsoApp.hom.naturality χ h φ)

/-- The forward component of the bundled equal-base comparison is its named
objectwise transport. -/
@[simp]
theorem Reindex.congrIso.hom.app
    {U V : C} {f g : V ⟶ U} (h : f = g) (x : Fiber p U) :
    (Reindex.congrIso χ h).hom.app x = (Reindex.congrIsoApp χ h x).hom := sorry

/-- The inverse component of the bundled equal-base comparison is its named
objectwise transport. -/
@[simp]
theorem Reindex.congrIso.inv.app
    {U V : C} {f g : V ⟶ U} (h : f = g) (x : Fiber p U) :
    (Reindex.congrIso χ h).inv.app x = (Reindex.congrIsoApp χ h x).inv := sorry

/-- Transporting a chosen reindexing object along an equality of base arrows identifies the
corresponding chosen cartesian arrows. This is the stable transport interface for calculations
that normalize composites only up to associativity. -/
theorem Reindex.congrIsoApp.cartesian.eqToHom
    {U V : C} {f g : V ⟶ U} (h : f = g) (x : Fiber p U) :
    Fiber.fiberInclusion.map
        (eqToHom (congrArg (fun r ↦ χ.reindexObj r x) h)) ≫
      χ.cartesianHom g x =
    χ.cartesianHom f x := sorry

/-- The named reindexing comparison along equal base arrows is characterized by its composite
with the chosen cartesian arrow. -/
@[reassoc]
theorem Reindex.congrIsoApp.hom.fac
    {U V : C} {f g : V ⟶ U} (h : f = g) (x : Fiber p U) :
    (Reindex.congrIsoApp χ h x).hom.1 ≫ χ.cartesianHom g x =
      χ.cartesianHom f x := sorry

/-- The inverse reindexing comparison along equal base arrows carries the selected cartesian
arrow over `f` to the selected cartesian arrow over `g`. -/
@[reassoc]
theorem Reindex.congrIsoApp.inv.fac
    {U V : C} {f g : V ⟶ U} (h : f = g) (x : Fiber p U) :
    (Reindex.congrIsoApp χ h x).inv.1 ≫ χ.cartesianHom f x =
      χ.cartesianHom g x := sorry

/-- The objectwise composition comparison for a specified composite `gf`. It first transports
reindexing along `gf` to reindexing along `g ≫ f`, then applies the canonical composition
comparison. -/
noncomputable def Reindex.specifiedCompIsoApp
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) (x : Fiber p D) :
    (χ.reindex gf).obj x ≅
      (χ.reindex g).obj ((χ.reindex f).obj x) :=
  Reindex.congrIsoApp χ hgf.symm x ≪≫ Reindex.compIsoApp χ f g x

/-- The forward specified-composite comparison factors the iterated cartesian arrows through the
selected cartesian arrow over `gf`. -/
@[reassoc]
theorem Reindex.specifiedCompIsoApp.hom.fac
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) (x : Fiber p D) :
    (Reindex.specifiedCompIsoApp χ f g gf hgf x).hom.1 ≫
        χ.cartesianHom g ((χ.reindex f).obj x) ≫
        χ.cartesianHom f x =
      χ.cartesianHom gf x := sorry

/-- The inverse specified-composite comparison factors the selected cartesian arrow over `gf`
through the two iterated cartesian arrows. -/
@[reassoc]
theorem Reindex.specifiedCompIsoApp.inv.fac
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) (x : Fiber p D) :
    (Reindex.specifiedCompIsoApp χ f g gf hgf x).inv.1 ≫
        χ.cartesianHom gf x =
      χ.cartesianHom g ((χ.reindex f).obj x) ≫
        χ.cartesianHom f x := sorry

/-- Naturality of the forward objectwise comparison over a specified composite. -/
theorem Reindex.specifiedCompIsoApp.hom.naturality
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) {x y : Fiber p D} (φ : x ⟶ y) :
    (χ.reindex gf).map φ ≫
        (Reindex.specifiedCompIsoApp χ f g gf hgf y).hom =
      (Reindex.specifiedCompIsoApp χ f g gf hgf x).hom ≫
        (χ.reindex f ⋙ χ.reindex g).map φ := sorry

/-- Naturality of the inverse objectwise comparison over a specified composite. -/
theorem Reindex.specifiedCompIsoApp.inv.naturality
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) {x y : Fiber p D} (φ : x ⟶ y) :
    (χ.reindex f ⋙ χ.reindex g).map φ ≫
        (Reindex.specifiedCompIsoApp χ f g gf hgf y).inv =
      (Reindex.specifiedCompIsoApp χ f g gf hgf x).inv ≫
        (χ.reindex gf).map φ := sorry

/-- Conjugating direct reindexing along a specified composite gives successive reindexing. -/
@[reassoc]
theorem Reindex.specifiedCompIsoApp.conjugation.toIterated
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) {x y : Fiber p D} (φ : x ⟶ y) :
    (Reindex.specifiedCompIsoApp χ f g gf hgf x).inv ≫
        (χ.reindex gf).map φ ≫
        (Reindex.specifiedCompIsoApp χ f g gf hgf y).hom =
      (χ.reindex f ⋙ χ.reindex g).map φ := sorry

/-- Conjugating successive reindexing by the specified-composite comparison recovers direct
reindexing. -/
@[reassoc]
theorem Reindex.specifiedCompIsoApp.conjugation.toComposite
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) {x y : Fiber p D} (φ : x ⟶ y) :
    (Reindex.specifiedCompIsoApp χ f g gf hgf x).hom ≫
        (χ.reindex f ⋙ χ.reindex g).map φ ≫
        (Reindex.specifiedCompIsoApp χ f g gf hgf y).inv =
      (χ.reindex gf).map φ := sorry

/-- A specified composite `gf = g ≫ f` induces a natural composition comparison between
reindexing functors. -/
@[stacks 02XN]
noncomputable def Reindex.specifiedCompIso
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) :
    χ.reindex gf ≅ χ.reindex f ⋙ χ.reindex g :=
  NatIso.ofComponents (Reindex.specifiedCompIsoApp χ f g gf hgf)
    (fun φ ↦ Reindex.specifiedCompIsoApp.hom.naturality χ f g gf hgf φ)

/-- The forward component of the bundled specified-composite comparison is its named
objectwise comparison. -/
@[simp]
theorem Reindex.specifiedCompIso.hom.app
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) (x : Fiber p D) :
    (Reindex.specifiedCompIso χ f g gf hgf).hom.app x =
      (Reindex.specifiedCompIsoApp χ f g gf hgf x).hom := sorry

/-- The inverse component of the bundled specified-composite comparison is its named
objectwise comparison. -/
@[simp]
theorem Reindex.specifiedCompIso.inv.app
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) (x : Fiber p D) :
    (Reindex.specifiedCompIso χ f g gf hgf).inv.app x =
      (Reindex.specifiedCompIsoApp χ f g gf hgf x).inv := sorry

end Functor.Cleavage

end CategoryTheory
