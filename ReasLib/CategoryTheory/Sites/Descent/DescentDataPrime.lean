/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Component isomorphisms of prime descent data

An isomorphism of `Pseudofunctor.DescentData'` is represented by a family of component
morphisms.  This leaf exposes the corresponding family of ordinary category isomorphisms, so
applications need not reconstruct it from the two inverse descent-data morphisms.
-/

@[expose] public section

universe t v' v u' u

namespace CategoryTheory

open Limits

namespace Pseudofunctor.DescentData'

variable {C : Type u} [Category.{v} C]
variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {ι : Type t} {U : C} {X : ι → C} {f : ∀ i, X i ⟶ U}
variable {sq : ∀ i j, ChosenPullback (f i) (f j)}
variable {sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃)}

/-- The hom and inverse components of an isomorphism of prime descent data compose to the
identity on the source component. -/
theorem iso_hom_inv_id
    {D₁ D₂ : F.DescentData' sq sq₃} (e : D₁ ≅ D₂) (i : ι) :
    e.hom.hom i ≫ e.inv.hom i = 𝟙 (D₁.obj i) := sorry

/-- The inverse and hom components of an isomorphism of prime descent data compose to the
identity on the target component. -/
theorem iso_inv_hom_id
    {D₁ D₂ : F.DescentData' sq sq₃} (e : D₁ ≅ D₂) (i : ι) :
    e.inv.hom i ≫ e.hom.hom i = 𝟙 (D₂.obj i) := sorry

/-- The ordinary category isomorphism at an index induced by an isomorphism of prime descent
data. -/
def componentIso
    {D₁ D₂ : F.DescentData' sq sq₃} (e : D₁ ≅ D₂) (i : ι) :
    D₁.obj i ≅ D₂.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := iso_hom_inv_id e i
  inv_hom_id := iso_inv_hom_id e i

/-- The forward morphism of `componentIso` is the corresponding component of the descent-data
isomorphism. -/
@[simp]
theorem componentIso_hom
    {D₁ D₂ : F.DescentData' sq sq₃} (e : D₁ ≅ D₂) (i : ι) :
    (componentIso e i).hom = e.hom.hom i := sorry

/-- The inverse morphism of `componentIso` is the corresponding component of the inverse
descent-data isomorphism. -/
@[simp]
theorem componentIso_inv
    {D₁ D₂ : F.DescentData' sq sq₃} (e : D₁ ≅ D₂) (i : ι) :
    (componentIso e i).inv = e.inv.hom i := sorry

end Pseudofunctor.DescentData'

end CategoryTheory
