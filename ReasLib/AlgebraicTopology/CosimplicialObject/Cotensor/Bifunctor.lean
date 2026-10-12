/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Cotensor.Index
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The unrestricted cosimplicial cotensor bifunctor
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable [HasCotensors.OfIndex (𝟭 SSet.{w}) C]

/-- Cotensor as a bifunctor, contravariant in arbitrary simplicial sets and covariant in
cosimplicial objects. -/
@[stacks 019V "cosimplicial cotensor bifunctor"]
abbrev cotensor.bifunctor :
    SSet.{w}ᵒᵖ ⥤ CosimplicialObject C ⥤ CosimplicialObject C :=
  cotensor.ofIndex (C := C) (𝟭 SSet.{w})

/-- Evaluating the cotensor bifunctor on both variables gives the corresponding cotensor. -/
@[simp, stacks 019V "cotensor bifunctor object formula"]
theorem cotensor.bifunctor.obj (U : SSet.{w}ᵒᵖ) (V : CosimplicialObject C) :
    ((cotensor.bifunctor (C := C)).obj U).obj V = cotensor U.unop V := sorry

/-- The action of the cotensor bifunctor on a morphism in the cosimplicial-object variable. -/
@[simp, stacks 019V "cotensor bifunctor object-variable map formula"]
theorem cotensor.bifunctor.obj.map (U : SSet.{w}ᵒᵖ)
    {V W : CosimplicialObject C} (f : V ⟶ W) :
    ((cotensor.bifunctor (C := C)).obj U).map f = cotensor.hom U.unop f := sorry

/-- The component of the cotensor bifunctor on a morphism in its simplicial-set variable. -/
@[simp, stacks 019V "cotensor bifunctor index-map formula"]
theorem cotensor.bifunctor.map.app {U W : SSet.{w}ᵒᵖ} (a : U ⟶ W)
    (V : CosimplicialObject C) :
    ((cotensor.bifunctor (C := C)).map a).app V = cotensor.indexHom V a.unop := sorry

end CategoryTheory.CosimplicialObject
