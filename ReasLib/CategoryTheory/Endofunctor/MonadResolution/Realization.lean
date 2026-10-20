module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Endofunctor.Iteration.Cosimplicial
import Mathlib.Tactic.CrossRefAttribute

/-!
# Realizations of iterated-endofunctor cosimplicial data

This leaf owns the assumption-minimal realization witness for prescribed positive iterates,
cofaces, and codegeneracies. It also owns stable degree isomorphisms, degree splitting, and the
unit-induced coaugmentation; no generator code or bundled monad is required.
-/

@[expose] public section

open CategoryTheory.CosimplicialObject
open CategoryTheory.Functor
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace EndofunctorResolution

/-- A cosimplicial object realizes the positive-iterate formulas determined by unit-like and
multiplication-like natural transformations. -/
@[stacks 0G5N "iterated-endofunctor cosimplicial realization witness"]
structure CosimplicialRealization {Y : C ⥤ C}
    (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y) (U : CosimplicialObject (C ⥤ C)) : Prop where
  /-- The degree-`n` object is the `(n + 1)`-fold positive iterate. -/
  obj_eq (n : ℕ) : U ^⦋n⦌ = Y ⁺⦋n⦌
  /-- The cofaces insert the unit-like transformation. -/
  δ_eq {n : ℕ} (i : Fin (n + 2)) :
    eqToHom (obj_eq n) ≫ IteratedEndofunctor.coface d n i =
      U.δ i ≫ eqToHom (obj_eq (n + 1))
  /-- The codegeneracies insert the multiplication-like transformation. -/
  σ_eq {n : ℕ} (i : Fin (n + 1)) :
    eqToHom (obj_eq (n + 1)) ≫ IteratedEndofunctor.codegeneracy s n i =
      U.σ i ≫ eqToHom (obj_eq n)

namespace CosimplicialRealization

/-- The stable isomorphism-valued degree identification of a cosimplicial realization. -/
@[stacks 0G5N "degree isomorphism of a cosimplicial endofunctor realization"]
def objIso {Y : C ⥤ C} {d : 𝟭 C ⟶ Y} {s : Y ⋙ Y ⟶ Y}
    {U : CosimplicialObject (C ⥤ C)} (hU : CosimplicialRealization d s U) (n : ℕ) :
    U ^⦋n⦌ ≅ Y ⁺⦋n⦌ :=
  eqToIso (hU.obj_eq n)

/-- The forward degree map is the transport supplied by the realization witness. -/
@[simp, stacks 0G5N "forward degree transport of a cosimplicial realization"]
theorem objIso.hom_eqToHom {Y : C ⥤ C} {d : 𝟭 C ⟶ Y} {s : Y ⋙ Y ⟶ Y}
    {U : CosimplicialObject (C ⥤ C)} (hU : CosimplicialRealization d s U) (n : ℕ) :
    (objIso hU n).hom = eqToHom (hU.obj_eq n) := sorry

/-- The inverse degree map is the reverse transport supplied by the realization witness. -/
@[simp, stacks 0G5N "inverse degree transport of a cosimplicial realization"]
theorem objIso.inv_eqToHom {Y : C ⥤ C} {d : 𝟭 C ⟶ Y} {s : Y ⋙ Y ⟶ Y}
    {U : CosimplicialObject (C ⥤ C)} (hU : CosimplicialRealization d s U) (n : ℕ) :
    (objIso hU n).inv = eqToHom (hU.obj_eq n).symm := sorry

/-- The degree isomorphisms identify realization cofaces with insertion of the unit-like map. -/
@[stacks 0G5N "coface formula through a cosimplicial realization"]
theorem objIso.δ {Y : C ⥤ C} {d : 𝟭 C ⟶ Y} {s : Y ⋙ Y ⟶ Y}
    {U : CosimplicialObject (C ⥤ C)} (hU : CosimplicialRealization d s U)
    {n : ℕ} (i : Fin (n + 2)) :
    (objIso hU n).hom ≫ IteratedEndofunctor.coface d n i =
      U.δ i ≫ (objIso hU (n + 1)).hom := sorry

/-- The degree isomorphisms identify realization codegeneracies with multiplication. -/
@[stacks 0G5N "codegeneracy formula through a cosimplicial realization"]
theorem objIso.σ {Y : C ⥤ C} {d : 𝟭 C ⟶ Y} {s : Y ⋙ Y ⟶ Y}
    {U : CosimplicialObject (C ⥤ C)} (hU : CosimplicialRealization d s U)
    {n : ℕ} (i : Fin (n + 1)) :
    (objIso hU (n + 1)).hom ≫ IteratedEndofunctor.codegeneracy s n i =
      U.σ i ≫ (objIso hU n).hom := sorry

/-- Split a realization degree into the two consecutive positive-iterate blocks selected by
`i`. -/
@[stacks 0G5R "factorization of a cosimplicial realization degree"]
def splitIso {Y : C ⥤ C} {d : 𝟭 C ⟶ Y} {s : Y ⋙ Y ⟶ Y}
    {U : CosimplicialObject (C ⥤ C)} (hU : CosimplicialRealization d s U)
    (n : ℕ) (i : Fin (n + 1)) :
    U ^⦋n + 1⦌ ≅ U ^⦋n - i.1⦌ ⋙ U ^⦋i.1⦌ :=
  hU.objIso (n + 1) ≪≫
    IteratedEndofunctor.splitIso Y n i ≪≫
    NatIso.hcomp (hU.objIso (n - i.1)).symm (hU.objIso i.1).symm

/-- The unit-like degree-zero map of a realization has equal composites with its two cofaces. -/
@[stacks 0G5N "cosimplicial realization zero-coface compatibility"]
theorem zero_coface {Y : C ⥤ C} {d : 𝟭 C ⟶ Y} {s : Y ⋙ Y ⟶ Y}
    {U : CosimplicialObject (C ⥤ C)} (hU : CosimplicialRealization d s U) :
    d ≫ (hU.objIso 0).inv ≫ U.δ 0 =
      d ≫ (hU.objIso 0).inv ≫ U.δ 1 := sorry

/-- The degree-zero coaugmentation map has equal composites along all maps out of the zero
simplex. -/
@[stacks 0G5N "cosimplicial realization coaugmentation compatibility"]
theorem coaugmentation_map_eq {Y : C ⥤ C} {d : 𝟭 C ⟶ Y} {s : Y ⋙ Y ⟶ Y}
    {U : CosimplicialObject (C ⥤ C)} (hU : CosimplicialRealization d s U)
    (Δ : SimplexCategory) (g₁ g₂ : ⦋0⦌ ⟶ Δ) :
    (d ≫ (hU.objIso 0).inv) ≫ U.map g₁ =
      (d ≫ (hU.objIso 0).inv) ≫ U.map g₂ := sorry

/-- The coaugmentation of a cosimplicial realization induced by its unit-like map. -/
@[stacks 0G5N "iterated-endofunctor coaugmentation"]
def coaugmentation {Y : C ⥤ C} {d : 𝟭 C ⟶ Y} {s : Y ⋙ Y ⟶ Y}
    {U : CosimplicialObject (C ⥤ C)} (hU : CosimplicialRealization d s U) :
    (const (C ⥤ C)).obj (𝟭 C) ⟶ U :=
  (U.augment (𝟭 C) (d ≫ (hU.objIso 0).inv) (coaugmentation_map_eq hU)).hom

/-- The induced coaugmentation has the specified degree-zero component. -/
@[simp, stacks 0G5N "cosimplicial realization coaugmentation degree-zero component"]
theorem coaugmentation.app_zero {Y : C ⥤ C} {d : 𝟭 C ⟶ Y} {s : Y ⋙ Y ⟶ Y}
    {U : CosimplicialObject (C ⥤ C)} (hU : CosimplicialRealization d s U) :
    (coaugmentation hU).app ⦋0⦌ = d ≫ (hU.objIso 0).inv := sorry

/-- A realization bundled with its unit-induced coaugmentation. -/
@[stacks 0G5N "augmented cosimplicial endofunctor realization"]
def augmented {Y : C ⥤ C} {d : 𝟭 C ⟶ Y} {s : Y ⋙ Y ⟶ Y}
    {U : CosimplicialObject (C ⥤ C)} (hU : CosimplicialRealization d s U) :
    CosimplicialObject.Augmented (C ⥤ C) where
  left := 𝟭 C
  right := U
  hom := coaugmentation hU

/-- The point of a bundled cosimplicial realization is the identity endofunctor. -/
@[simp, stacks 0G5N "point of an augmented cosimplicial realization"]
theorem augmented.left {Y : C ⥤ C} {d : 𝟭 C ⟶ Y} {s : Y ⋙ Y ⟶ Y}
    {U : CosimplicialObject (C ⥤ C)} (hU : CosimplicialRealization d s U) :
    hU.augmented.left = 𝟭 C := sorry

/-- The cosimplicial component of a bundled realization is the realized object. -/
@[simp, stacks 0G5N "cosimplicial component of an augmented realization"]
theorem augmented.right {Y : C ⥤ C} {d : 𝟭 C ⟶ Y} {s : Y ⋙ Y ⟶ Y}
    {U : CosimplicialObject (C ⥤ C)} (hU : CosimplicialRealization d s U) :
    hU.augmented.right = U := sorry

/-- The structure map of a bundled realization is its unit-induced coaugmentation. -/
@[simp, stacks 0G5N "map of an augmented cosimplicial realization"]
theorem augmented.hom {Y : C ⥤ C} {d : 𝟭 C ⟶ Y} {s : Y ⋙ Y ⟶ Y}
    {U : CosimplicialObject (C ⥤ C)} (hU : CosimplicialRealization d s U) :
    hU.augmented.hom = coaugmentation hU := sorry

end CosimplicialRealization

end EndofunctorResolution

end CategoryTheory
