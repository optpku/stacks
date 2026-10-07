module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmentation
public import ReasLib.CategoryTheory.Endofunctor.Iteration.Simplicial
import Mathlib.Tactic.CrossRefAttribute

/-!
# Realizations of iterated-endofunctor simplicial data

This leaf owns the assumption-minimal realization witness for prescribed positive iterates,
faces, and degeneracies. It also owns stable degree isomorphisms, degree splitting, and the
counit-induced augmentation; no generator code or bundled comonad is required.
-/

@[expose] public section

open Opposite
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Augmentation
open CategoryTheory.Functor
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace EndofunctorResolution

/-- A simplicial object realizes the iterated endofunctor construction when its objects, faces,
and degeneracies agree with the explicit positive-iterate formulas. -/
@[stacks 0G5N "iterated-endofunctor realization witness"]
structure Realization {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (U : SimplicialObject (C ⥤ C)) : Prop where
  /-- The degree-`n` object is the `(n + 1)`-fold positive iterate. -/
  obj_eq (n : ℕ) : U _⦋n⦌ = Y ⁺⦋n⦌
  /-- The faces insert the counit-like transformation. -/
  δ_eq {n : ℕ} (i : Fin (n + 2)) :
    eqToHom (obj_eq (n + 1)) ≫ IteratedEndofunctor.face d n i =
      U.δ i ≫ eqToHom (obj_eq n)
  /-- The degeneracies insert the comultiplication-like transformation. -/
  σ_eq {n : ℕ} (i : Fin (n + 1)) :
    eqToHom (obj_eq n) ≫ IteratedEndofunctor.degeneracy s n i =
      U.σ i ≫ eqToHom (obj_eq (n + 1))

namespace Realization

/-- The stable isomorphism-valued view of a realization's degree identification. Downstream
constructions should use this owner instead of rebuilding `eqToIso` from `obj_eq`. -/
@[stacks 0G5N "degree isomorphism of an iterated-endofunctor realization"]
def objIso {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
    {U : SimplicialObject (C ⥤ C)} (hU : Realization d s U) (n : ℕ) :
    U _⦋n⦌ ≅ Y ⁺⦋n⦌ :=
  eqToIso (hU.obj_eq n)

/-- The forward map of `objIso` is the transport supplied by the realization witness. -/
@[simp, stacks 0G5N "forward degree transport of a realization"]
theorem objIso.hom_eqToHom {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
    {U : SimplicialObject (C ⥤ C)} (hU : Realization d s U) (n : ℕ) :
    (objIso hU n).hom = eqToHom (hU.obj_eq n) := sorry

/-- The inverse map of `objIso` is the reverse transport supplied by the realization witness. -/
@[simp, stacks 0G5N "inverse degree transport of a realization"]
theorem objIso.inv_eqToHom {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
    {U : SimplicialObject (C ⥤ C)} (hU : Realization d s U) (n : ℕ) :
    (objIso hU n).inv = eqToHom (hU.obj_eq n).symm := sorry

/-- The degree isomorphisms identify realization faces with insertion of the counit-like map. -/
@[stacks 0G5N "face formula through the realization degree isomorphism"]
theorem objIso.δ {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
    {U : SimplicialObject (C ⥤ C)} (hU : Realization d s U)
    {n : ℕ} (i : Fin (n + 2)) :
    (objIso hU (n + 1)).hom ≫ IteratedEndofunctor.face d n i =
      U.δ i ≫ (objIso hU n).hom := sorry

/-- The degree isomorphisms identify realization degeneracies with insertion of the
comultiplication-like map. -/
@[stacks 0G5N "degeneracy formula through the realization degree isomorphism"]
theorem objIso.σ {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
    {U : SimplicialObject (C ⥤ C)} (hU : Realization d s U)
    {n : ℕ} (i : Fin (n + 1)) :
    (objIso hU n).hom ≫ IteratedEndofunctor.degeneracy s n i =
      U.σ i ≫ (objIso hU (n + 1)).hom := sorry

/-- Split degree `n + 1` of an iterated-endofunctor realization into the two consecutive
degree blocks selected by `i`. -/
@[stacks 0G5R "factorization of a realization degree"]
def splitIso {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
    {X : SimplicialObject (C ⥤ C)} (hX : Realization d s X)
    (n : ℕ) (i : Fin (n + 1)) :
    X _⦋n + 1⦌ ≅ X _⦋n - i.1⦌ ⋙ X _⦋i.1⦌ :=
  hX.objIso (n + 1) ≪≫
    IteratedEndofunctor.splitIso Y n i ≪≫
    NatIso.hcomp
      (hX.objIso (n - i.1)).symm
      (hX.objIso i.1).symm

/-- The degree-zero counit-like map of a realization equalizes its two faces. -/
@[stacks 0G5N "realization zero-face compatibility"]
theorem zero_face {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
    {U : SimplicialObject (C ⥤ C)}
    (hU : Realization d s U) :
    U.δ 0 ≫ (hU.objIso 0).hom ≫ d =
      U.δ 1 ≫ (hU.objIso 0).hom ≫ d := sorry

/-- The augmentation of a realization induced by its counit-like map. -/
@[stacks 0G5N "iterated-endofunctor augmentation"]
def augmentation {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
    {U : SimplicialObject (C ⥤ C)}
    (hU : Realization d s U) :
    U ⟶ (const (C ⥤ C)).obj (𝟭 C) :=
  ofZeroSimplex
    ⟨(hU.objIso 0).hom ≫ d,
      zero_face hU⟩

/-- The induced augmentation has the specified degree-zero component. -/
@[simp, stacks 0G5N "realization augmentation degree-zero component"]
theorem augmentation.app_zero {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
    {U : SimplicialObject (C ⥤ C)}
    (hU : Realization d s U) :
    (augmentation hU).app (op ⦋0⦌) =
      (hU.objIso 0).hom ≫ d := sorry

/-- A realization together with its counit-induced augmentation, as a bundled augmented
simplicial object. -/
@[stacks 0G5N "augmented iterated-endofunctor realization"]
def augmented {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
    {U : SimplicialObject (C ⥤ C)} (hU : Realization d s U) :
    SimplicialObject.Augmented (C ⥤ C) where
  left := U
  right := 𝟭 C
  hom := augmentation hU

/-- The simplicial-object component of a bundled realization is the realized object. -/
@[simp, stacks 0G5N "simplicial component of an augmented realization"]
theorem augmented.left {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
    {U : SimplicialObject (C ⥤ C)} (hU : Realization d s U) :
    hU.augmented.left = U := sorry

/-- The augmentation point of a bundled realization is the identity endofunctor. -/
@[simp, stacks 0G5N "point of an augmented realization"]
theorem augmented.right {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
    {U : SimplicialObject (C ⥤ C)} (hU : Realization d s U) :
    hU.augmented.right = 𝟭 C := sorry

/-- The structure map of a bundled realization is its counit-induced augmentation. -/
@[simp, stacks 0G5N "map of an augmented realization"]
theorem augmented.hom {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
    {U : SimplicialObject (C ⥤ C)} (hU : Realization d s U) :
    hU.augmented.hom = augmentation hU := sorry

end Realization

end EndofunctorResolution

end CategoryTheory
