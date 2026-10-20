/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Elements
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Reindex
public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiber-object presheaves

This leaf constructs the choice-independent presheaf of objects in the fibers
of a discrete fibration and exposes its intrinsic reindexing API.
-/

@[expose] public section

universe w u v uS vS

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace Functor

variable {S : Type uS} [Category.{vS} S]

section FiberObjectPresheafImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The transparent restriction function used to assemble `fiberObjectPresheaf`. It is the
intrinsic reindexing function determined by unique lifting, so no auxiliary cleavage is selected.
Transparency lets category-of-elements morphisms expose their defining reindexing equality
without passing through a propositional computation theorem. -/
private noncomputable abbrev fiberObjectRestriction
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] {U V : Cᵒᵖ} (f : U ⟶ V) :
    p.Fiber (unop U) ⟶ p.Fiber (unop V) :=
  TypeCat.ofHom (IsDiscreteFibration.reindexObj p f.unop)

/-- Raw restriction along an identity is the identity.

Proof strategy: apply `TypeCat.Hom.ext` and then
`IsDiscreteFibration.reindexObj.id`. -/
private theorem fiberObjectRestriction_id
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] (U : Cᵒᵖ) :
    fiberObjectRestriction p (𝟙 U) = 𝟙 (p.Fiber (unop U)) := sorry

/-- Raw restriction of fiber objects is contravariantly functorial.

Proof strategy: apply `TypeCat.Hom.ext` pointwise and use
`IsDiscreteFibration.reindexObj.comp` with the unopposite arrows. -/
private theorem fiberObjectRestriction_comp
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] {U V W : Cᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    fiberObjectRestriction p (f ≫ g) =
      fiberObjectRestriction p f ≫ fiberObjectRestriction p g := sorry

end Implementation

/-- The presheaf `U ↦ p.Fiber U` of objects in the discrete fibers of `p`. Its restriction maps
are the uniquely determined object actions of cartesian reindexing.

The definition is reducible so that a morphism in its category of elements carries, without a
propositional rewrite, the equality identifying its source with the intrinsic reindexing object. -/
@[reducible, stacks 02Y2 "fiber-object presheaf"]
noncomputable def fiberObjectPresheaf
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] : Cᵒᵖ ⥤ Type uS where
  obj U := p.Fiber (unop U)
  map f := Implementation.fiberObjectRestriction p f
  map_id U := Implementation.fiberObjectRestriction_id p U
  map_comp f g := Implementation.fiberObjectRestriction_comp p f g

/- Axiom audit: the object types are explicit and the restriction functions use only the
choice-independent specification of `IsDiscreteFibration.reindexObj`; their non-`Prop` data depend
only on `Classical.choice`. The `sorryAx` dependency is confined to the Prop-valued
identity/composition laws. -/

end FiberObjectPresheafImplementation

/-- The value of the fiber-object presheaf at `U` is the standard fiber over `unop U`. -/
@[simp]
theorem fiberObjectPresheaf.obj
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] (U : Cᵒᵖ) :
    p.fiberObjectPresheaf.obj U = p.Fiber (unop U) := sorry
/- Proof strategy: unfold only the object projection of `fiberObjectPresheaf`. -/

/-- The restriction map of `fiberObjectPresheaf` evaluates to the intrinsic reindexing determined
by unique lifting. This is the canonical computation rule; no cleavage occurs in its surface. -/
@[simp]
theorem fiberObjectPresheaf.map_apply
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : p.Fiber (unop U)) :
    p.fiberObjectPresheaf.map f x =
      IsDiscreteFibration.reindexObj p f.unop x := sorry
/- Proof strategy: unfold the map projection and the private restriction function. -/

/-- The restriction map of `fiberObjectPresheaf` may be computed with any cleavage.

This is the choice-independence specification: two cartesian reindexings are isomorphic, and
strict discreteness of the target fiber turns that isomorphism into equality of objects.

Proof strategy: compare the default and supplied cartesian lifts by their canonical vertical
isomorphism, then apply `obj_ext_of_isDiscrete` in the target fiber. -/
theorem fiberObjectPresheaf.map_eq_reindex
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] (χ : p.Cleavage)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : p.Fiber (unop U)) :
    p.fiberObjectPresheaf.map f x = (f.unop)⁎[χ] x := sorry

namespace fiberObjectPresheaf

/-- A total morphism identifies the tautological fiber object of its codomain, reindexed along
its projected base map, with the tautological fiber object of its domain. -/
theorem tautologicalSection.naturality
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {x y : Sᵒᵖ} (f : x ⟶ y) :
    p.fiberObjectPresheaf.map (p.map f.unop).op ⟨x.unop, rfl⟩ =
      ⟨y.unop, rfl⟩ := sorry

/-- The tautological section of the fiber-object presheaf pulled back to the total category.
At a total object it records that object with its reflexive fiber witness. -/
@[stacks 02Y2 "tautological fiber-object section",
  stacks 04SI "tautological fiber-object section"]
noncomputable def tautologicalSection
  (p : S ⥤ C) [Functor.IsDiscreteFibration p] :
    (p.op ⋙ p.fiberObjectPresheaf).sections :=
  ⟨fun x => ⟨x.unop, rfl⟩,
    fun f => tautologicalSection.naturality p f⟩

/-- The tautological section evaluates to the displayed object in its own standard fiber. -/
@[simp]
theorem tautologicalSection.apply
    (p : S ⥤ C) [Functor.IsDiscreteFibration p] (x : Sᵒᵖ) :
    (tautologicalSection p).1 x = ⟨x.unop, rfl⟩ := sorry

end fiberObjectPresheaf

/-- The intrinsic cartesian arrow whose source is presented exactly as the value of
`fiberObjectPresheaf.map`. This transparent endpoint form is convenient for constructions out of
the category of elements. -/
@[stacks 02Y2 "intrinsic arrow for fiber-object restriction"]
noncomputable def fiberObjectPresheaf.cartesianHom
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : p.Fiber (unop U)) :
    (p.fiberObjectPresheaf.map f x).1 ⟶ x.1 :=
  IsDiscreteFibration.cartesianHom p f.unop x

/- Axiom audit: the morphism is the explicit intrinsic cartesian arrow and its non-`Prop` payload
depends only on `Classical.choice`; no propositional computation theorem is used to align its
domain. The whole declaration inherits `sorryAx` only from the functor-law fields of
`fiberObjectPresheaf` occurring in its endpoint type. -/

/-- `fiberObjectPresheaf.cartesianHom` is the intrinsic cartesian arrow selected by unique
lifting. -/
@[simp]
theorem fiberObjectPresheaf.cartesianHom.eq_intrinsic
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : p.Fiber (unop U)) :
    fiberObjectPresheaf.cartesianHom p f x =
      IsDiscreteFibration.cartesianHom p f.unop x := sorry
/- Proof strategy: unfold `fiberObjectPresheaf.cartesianHom`; reducibility of
`fiberObjectPresheaf` aligns the source objects definitionally. -/

/-- The endpoint-aligned cartesian arrow is strongly cartesian over the displayed base
morphism. -/
instance fiberObjectPresheaf.cartesianHom.isStronglyCartesian
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : p.Fiber (unop U)) :
    p.IsStronglyCartesian f.unop
      (fiberObjectPresheaf.cartesianHom p f x) := sorry
/- Proof strategy: rewrite by
`fiberObjectPresheaf.cartesianHom.eq_intrinsic` and use the intrinsic cartesian-arrow
instance. -/

/-- The projection of the endpoint-aligned cartesian arrow is the displayed base morphism, with
the endpoint transports stored by the two fiber objects. -/
@[simp]
theorem fiberObjectPresheaf.cartesianHom.map
    (p : S ⥤ C) [Functor.IsDiscreteFibration p]
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : p.Fiber (unop U)) :
    p.map (fiberObjectPresheaf.cartesianHom p f x) =
      eqToHom (p.fiberObjectPresheaf.map f x).2 ≫
        f.unop ≫ eqToHom x.2.symm := sorry
/- Proof strategy: rewrite the arrow by
`fiberObjectPresheaf.cartesianHom.eq_intrinsic` and apply `cartesianHom.map`; reducibility of
`fiberObjectPresheaf` aligns the source witness. -/

end Functor

end CategoryTheory
