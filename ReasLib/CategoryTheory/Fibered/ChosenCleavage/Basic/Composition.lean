module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Core

/-!
# Chosen-cleavage reindexing composition

This leaf owns the selected composition and identity comparisons for reindexing
functors, together with their component computations and naturality.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor

/-- The selected objectwise comparison `(g ≫ f)⁎x ≅ g⁎(f⁎x)`. -/
noncomputable def Chosen.Reindex.compIsoApp (p : S ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U) :
    (Chosen.reindex p (g ≫ f)).obj x ≅
      (Chosen.reindex p g).obj ((Chosen.reindex p f).obj x) :=
  Cleavage.Reindex.compIsoApp (Cleavage.ofIsFibered p) f g x

/-- The forward selected composition comparison is characterized by its composite with the two
selected cartesian arrows. -/
@[reassoc]
theorem Chosen.Reindex.compIsoApp.hom.fac (p : S ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U) :
    (Chosen.Reindex.compIsoApp p f g x).hom.1 ≫
        Chosen.cartesianHom p g ((Chosen.reindex p f).obj x) ≫
        Chosen.cartesianHom p f x =
      Chosen.cartesianHom p (g ≫ f) x := sorry

/-- The inverse selected composition comparison factors the selected composite cartesian arrow
through the two selected cartesian arrows. -/
@[reassoc]
theorem Chosen.Reindex.compIsoApp.inv.fac (p : S ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U) :
    (Chosen.Reindex.compIsoApp p f g x).inv.1 ≫
        Chosen.cartesianHom p (g ≫ f) x =
      Chosen.cartesianHom p g ((Chosen.reindex p f).obj x) ≫
        Chosen.cartesianHom p f x := sorry

/-- Naturality of the selected objectwise composition comparison. -/
theorem Chosen.Reindex.compIsoApp.hom.naturality (p : S ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {x y : p.Fiber U} (φ : x ⟶ y) :
    (Chosen.reindex p (g ≫ f)).map φ ≫
        (Chosen.Reindex.compIsoApp p f g y).hom =
      (Chosen.Reindex.compIsoApp p f g x).hom ≫
        (Chosen.reindex p f ⋙ Chosen.reindex p g).map φ := sorry

/-- Inverse naturality of the selected objectwise composition comparison. -/
theorem Chosen.Reindex.compIsoApp.inv.naturality (p : S ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {x y : p.Fiber U} (φ : x ⟶ y) :
    (Chosen.reindex p f ⋙ Chosen.reindex p g).map φ ≫
        (Chosen.Reindex.compIsoApp p f g y).inv =
      (Chosen.Reindex.compIsoApp p f g x).inv ≫
        (Chosen.reindex p (g ≫ f)).map φ := sorry

/-- The selected composition comparisons bundle into a natural isomorphism of reindexing
functors. -/
@[stacks 02XN]
noncomputable def Chosen.Reindex.compIso (p : S ⥤ C) [p.IsFibered]
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    Chosen.reindex p (g ≫ f) ≅ Chosen.reindex p f ⋙ Chosen.reindex p g :=
  Cleavage.Reindex.compIso (Cleavage.ofIsFibered p) f g

/-- The selected unit comparison at a fiber object. -/
noncomputable def Chosen.Reindex.idIsoApp (p : S ⥤ C) [p.IsFibered]
    (U : C) (x : p.Fiber U) :
    x ≅ (Chosen.reindex p (𝟙 U)).obj x :=
  Cleavage.Reindex.idIsoApp (Cleavage.ofIsFibered p) U x

/-- The forward selected unit comparison factors the selected cartesian arrow over the
identity through the identity of the fiber object. -/
@[reassoc]
theorem Chosen.Reindex.idIsoApp.hom.fac (p : S ⥤ C) [p.IsFibered]
    (U : C) (x : p.Fiber U) :
    (Chosen.Reindex.idIsoApp p U x).hom.1 ≫
        Chosen.cartesianHom p (𝟙 U) x =
      𝟙 (x.1) := sorry

/-- The inverse selected unit comparison is the selected cartesian arrow over the identity. -/
@[simp, reassoc]
theorem Chosen.Reindex.idIsoApp.inv.eq_cartesianHom (p : S ⥤ C) [p.IsFibered]
    (U : C) (x : p.Fiber U) :
    (Chosen.Reindex.idIsoApp p U x).inv.1 =
      Chosen.cartesianHom p (𝟙 U) x := sorry

/-- Naturality of the selected unit comparison. -/
theorem Chosen.Reindex.idIsoApp.hom.naturality (p : S ⥤ C) [p.IsFibered]
    (U : C) {x y : p.Fiber U} (φ : x ⟶ y) :
    φ ≫ (Chosen.Reindex.idIsoApp p U y).hom =
      (Chosen.Reindex.idIsoApp p U x).hom ≫
        (Chosen.reindex p (𝟙 U)).map φ := sorry

/-- Inverse naturality of the selected unit comparison. -/
theorem Chosen.Reindex.idIsoApp.inv.naturality (p : S ⥤ C) [p.IsFibered]
    (U : C) {x y : p.Fiber U} (φ : x ⟶ y) :
    (Chosen.reindex p (𝟙 U)).map φ ≫
        (Chosen.Reindex.idIsoApp p U y).inv =
      (Chosen.Reindex.idIsoApp p U x).inv ≫ φ := sorry

/-- Conjugating a fiber morphism by the selected unit comparison gives its selected identity
reindexing. -/
@[reassoc]
theorem Chosen.Reindex.idIsoApp.conjugation.toReindex
    (p : S ⥤ C) [p.IsFibered]
    (U : C) {x y : p.Fiber U} (φ : x ⟶ y) :
    (Chosen.Reindex.idIsoApp p U x).inv ≫ φ ≫
        (Chosen.Reindex.idIsoApp p U y).hom =
      Chosen.reindexMap p (𝟙 U) φ := sorry

/-- Conjugating selected identity reindexing by the selected unit comparison recovers the
original fiber morphism. -/
@[reassoc]
theorem Chosen.Reindex.idIsoApp.conjugation.toIdentity
    (p : S ⥤ C) [p.IsFibered]
    (U : C) {x y : p.Fiber U} (φ : x ⟶ y) :
    (Chosen.Reindex.idIsoApp p U x).hom ≫
        Chosen.reindexMap p (𝟙 U) φ ≫
        (Chosen.Reindex.idIsoApp p U y).inv =
      φ := sorry

/-- The selected unit comparisons bundle into a natural isomorphism. -/
@[stacks 02XN]
noncomputable def Chosen.Reindex.idIso (p : S ⥤ C) [p.IsFibered] (U : C) :
    𝟭 (p.Fiber U) ≅ Chosen.reindex p (𝟙 U) :=
  Cleavage.Reindex.idIso (Cleavage.ofIsFibered p) U

/-- Selected reindexing along a base morphism with a section is faithful. -/
theorem Chosen.reindex.faithfulOfSection (p : S ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (s : U ⟶ V) (hs : s ≫ f = 𝟙 U) :
    Functor.Faithful (Chosen.reindex p f) := sorry

end Functor

end CategoryTheory
