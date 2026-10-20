/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Functor
public import ReasLib.CategoryTheory.Functor.IsomorphismClasses
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiberwise isomorphism-class presheaves

This leaf constructs the choice-independent presheaf of isomorphism classes in
the fibers of an arbitrary fibred category.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace Functor

variable {S : Type uS} [Category.{vS} S]

namespace fiberIsoClassPresheaf

/-- The raw restriction function on fiberwise isomorphism classes used to assemble the
fiber-class presheaf. Its dependence on the default cleavage disappears after quotienting. -/
noncomputable def restriction
    (p : S ⥤ C) [p.IsFibered] {U V : Cᵒᵖ} (f : U ⟶ V) :
    isomorphismClasses.obj (Cat.of (p.Fiber (unop U))) ⟶
      isomorphismClasses.obj (Cat.of (p.Fiber (unop V))) :=
  TypeCat.ofHom ((f.unop)⁎[Cleavage.ofIsFibered p]).isoClassesMap

/-- Pullback along an identity acts trivially on fiberwise isomorphism classes. -/
@[simp]
theorem restriction.id
    (p : S ⥤ C) [p.IsFibered] (U : Cᵒᵖ) :
    restriction p (𝟙 U) = 𝟙 _ := sorry

/-- Pullback on fiberwise isomorphism classes is contravariantly functorial in the base map. -/
@[simp]
theorem restriction.comp
    (p : S ⥤ C) [p.IsFibered] {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    restriction p (f ≫ g) = restriction p f ≫ restriction p g := sorry

end fiberIsoClassPresheaf

/-- The presheaf sending `U` to the set of isomorphism classes of objects in the fiber
`p.Fiber U`, with restriction induced by cartesian pullback. Although its construction uses the
default cleavage, any cleavage gives the same restriction on the quotient; see
`fiberIsoClassPresheaf.map_mk`.
-/
noncomputable def fiberIsoClassPresheaf
    (p : S ⥤ C) [p.IsFibered] : Cᵒᵖ ⥤ Type uS where
  obj U := isomorphismClasses.obj (Cat.of (p.Fiber (unop U)))
  map f := fiberIsoClassPresheaf.restriction p f
  map_id U := fiberIsoClassPresheaf.restriction.id p U
  map_comp f g := fiberIsoClassPresheaf.restriction.comp p f g

attribute [stacks 0045 "fiberwise isomorphism-class presheaf"] fiberIsoClassPresheaf
attribute [stacks 0432 "fiberwise isomorphism-class presheaf"] fiberIsoClassPresheaf
/- Axiom audit: the object and restriction functions are explicit. The restriction inherits
`sorryAx` only from the Prop-valued identity/composition fields of `Cleavage.reindex`; its
underlying `reindexObj` and `reindexMap` data are clean. Quotient data use only the expected
`Classical.choice` and `Quot.sound`. -/

namespace fiberIsoClassPresheaf

/-- The value at `U` is the type of isomorphism classes in the standard fiber over `unop U`. -/
@[simp]
theorem obj
    (p : S ⥤ C) [p.IsFibered] (U : Cᵒᵖ) :
    (fiberIsoClassPresheaf p).obj U =
      isomorphismClasses.obj (Cat.of (p.Fiber (unop U))) := sorry

/-- Restriction of a represented fiberwise isomorphism class may be computed using any cleavage.

This is the choice-independence specification for `fiberIsoClassPresheaf`: different cartesian
lift choices yield isomorphic reindexed fiber objects, hence the same quotient class. -/
theorem map_mk
    (p : S ⥤ C) [p.IsFibered] (χ : p.Cleavage)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : p.Fiber (unop U)) :
    (fiberIsoClassPresheaf p).map f (Quotient.mk'' x) =
      Quotient.mk'' ((f.unop)⁎[χ] x) := sorry

/-- A total morphism identifies the class of its codomain, reindexed along its projected base
map, with the class of its domain. This is the naturality equation for the tautological section
of the fiberwise isomorphism-class presheaf. -/
theorem tautologicalSection.naturality
    (p : S ⥤ C) [p.IsFibered] {a b : Sᵒᵖ} (f : a ⟶ b) :
    (fiberIsoClassPresheaf p).map (p.map f.unop).op
        (Quotient.mk'' ⟨a.unop, rfl⟩) =
      Quotient.mk'' ⟨b.unop, rfl⟩ := sorry

/-- The tautological section of the fiberwise isomorphism-class presheaf pulled back to the
total category. At a total object it records that object's class in its own standard fiber. -/
@[stacks 0045 "tautological fiberwise isomorphism-class section"]
noncomputable def tautologicalSection
  (p : S ⥤ C) [p.IsFibered] :
    (p.op ⋙ fiberIsoClassPresheaf p).sections :=
  ⟨fun a => Quotient.mk'' ⟨a.unop, rfl⟩,
    fun f => tautologicalSection.naturality p f⟩

/-- The tautological section evaluates to the class of the displayed total object. -/
@[simp]
theorem tautologicalSection.apply
    (p : S ⥤ C) [p.IsFibered] (a : Sᵒᵖ) :
    (tautologicalSection p).1 a = Quotient.mk'' ⟨a.unop, rfl⟩ := sorry

end fiberIsoClassPresheaf

end Functor

end CategoryTheory
