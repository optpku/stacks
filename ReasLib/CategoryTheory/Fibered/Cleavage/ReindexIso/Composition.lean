/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
    p.IsHomLift (𝟙 W) (Reindex.compAmbientIso χ f g x).hom := sorry

/-- The inverse ambient composition comparison lies over `𝟙 W`. -/
theorem Reindex.compAmbientIso.inv.isHomLift
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    p.IsHomLift (𝟙 W) (Reindex.compAmbientIso χ f g x).inv := sorry

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
      χ.cartesianHom (g ≫ f) x := sorry
/- Proof strategy: unfold `Reindex.compIsoApp`; the statement is exactly
`IsCartesian.fac` for `IsCartesian.domainUniqueUpToIso`. -/

/-- The inverse composition-comparison component factors the chosen composite pullback map
through the iterated pullback maps. -/
@[reassoc]
theorem Reindex.compIsoApp.inv.fac
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    (Reindex.compIsoApp χ f g x).inv.1 ≫ χ.cartesianHom (g ≫ f) x =
      χ.cartesianHom g (f⁎[χ] x) ≫ χ.cartesianHom f x := sorry
/- Proof strategy: insert `Reindex.compIsoApp.hom.fac`, reassociate, and cancel the
inverse-hom pair of `Reindex.compIsoApp`. -/

/-- Naturality of the componentwise composition comparison. -/
theorem Reindex.compIsoApp.hom.naturality
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {x y : Fiber p U} (φ : x ⟶ y) :
    ((g ≫ f)⁎[χ]).map φ ≫ (Reindex.compIsoApp χ f g y).hom =
      (Reindex.compIsoApp χ f g x).hom ≫
        (f⁎[χ] ⋙ g⁎[χ]).map φ := sorry
/- Proof strategy: forget both morphisms to `S`, postcompose with the iterated cartesian
arrow, and use `reindexMap.fac` and `Reindex.compIsoApp.hom.fac`; cartesian uniqueness
then proves equality in the fiber. -/

/-- Inverse naturality of the componentwise composition comparison. This is the rewrite
orientation used when a morphism has already been reindexed successively. -/
theorem Reindex.compIsoApp.inv.naturality
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {x y : Fiber p U} (φ : x ⟶ y) :
    (f⁎[χ] ⋙ g⁎[χ]).map φ ≫ (Reindex.compIsoApp χ f g y).inv =
      (Reindex.compIsoApp χ f g x).inv ≫
        ((g ≫ f)⁎[χ]).map φ := sorry

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
    (Reindex.compIso χ f g).hom.app x = (Reindex.compIsoApp χ f g x).hom := sorry

/-- The inverse component of the bundled composition comparison is its named
objectwise comparison. -/
@[simp]
theorem Reindex.compIso.inv.app
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    (Reindex.compIso χ f g).inv.app x = (Reindex.compIsoApp χ f g x).inv := sorry

/-- The composition comparison is uniquely characterized by its cartesian factorization. -/
theorem Reindex.compIso.unique
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (α : (g ≫ f)⁎[χ] ≅ f⁎[χ] ⋙ g⁎[χ])
    (hα : ∀ x : Fiber p U,
      (α.hom.app x).1 ≫ χ.cartesianHom g (f⁎[χ] x) ≫ χ.cartesianHom f x =
        χ.cartesianHom (g ≫ f) x) :
    α = Reindex.compIso χ f g := sorry
/- Proof strategy: ext objectwise, forget to `S`, and apply cartesian uniqueness after
postcomposing both candidates with the iterated cartesian arrow. -/

end Functor.Cleavage

end CategoryTheory
