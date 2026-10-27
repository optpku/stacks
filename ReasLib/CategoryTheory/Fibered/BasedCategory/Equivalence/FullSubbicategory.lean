/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Bicategorical

/-!
# Based equivalences in full subbicategories

The neutral lift from an equivalence of based categories over a fixed base to an equivalence in
any full subbicategory of `BasedCategory C`.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open BasedCategory
open BasedFunctor
open ObjectProperty
open scoped Bicategory

universe u v w vS

variable {C : Type u} [Category.{v} C]

namespace ObjectProperty.FullSubbicategory

variable {P : ObjectProperty (BasedCategory.{vS, w} C)}
variable {X Y : P.FullSubbicategory}

/-- Lift explicit based quasi-inverse data for an owner morphism to an equivalence in any full
subbicategory of `BasedCategory C`.

The ambient bicategorical equivalence is owned by `BasedFunctor.QuasiInverse.toEquivalence`; the
full-subbicategory lift retains that data without selecting a second inverse. -/
noncomputable def equivalenceOfQuasiInverse
    (F : X ⟶ Y) (e : BasedFunctor.QuasiInverse F.hom) :
    X ≌ Y :=
  equivalenceOfAmbient e.toEquivalence

/-- The forward morphism of `equivalenceOfQuasiInverse` is the supplied owner morphism. -/
@[simp]
theorem equivalenceOfQuasiInverse.hom
    (F : X ⟶ Y) (e : BasedFunctor.QuasiInverse F.hom) :
    (equivalenceOfQuasiInverse F e).hom = F := rfl

/-- The inverse morphism of `equivalenceOfQuasiInverse` is the induced lift of the supplied
based quasi-inverse. -/
@[simp]
theorem equivalenceOfQuasiInverse.inv
    (F : X ⟶ Y) (e : BasedFunctor.QuasiInverse F.hom) :
    (equivalenceOfQuasiInverse F e).inv =
      Bicategory.InducedBicategory.mkHom e.inverse := rfl

/-- Interpret an owner morphism whose underlying based functor is an equivalence as an equivalence
in the full subbicategory. -/
noncomputable def asEquivalence
    (F : X ⟶ Y) [BasedFunctor.IsEquivalence F.hom] :
    X ≌ Y :=
  equivalenceOfQuasiInverse F F.hom.asQuasiInverse

/-- Package an explicit proof of equivalence of the underlying based functor without introducing
a local instance. -/
noncomputable def asEquivalenceOf
    (F : X ⟶ Y) (h : BasedFunctor.IsEquivalence F.hom) :
    X ≌ Y :=
  equivalenceOfAmbient (F.hom.asEquivalenceOf h)

/-- The forward morphism of `asEquivalence` is the supplied owner morphism. -/
@[simp]
theorem asEquivalence.hom
    (F : X ⟶ Y) [BasedFunctor.IsEquivalence F.hom] :
    (asEquivalence F).hom = F := rfl

/-- The inverse morphism of `asEquivalence` is the induced lift of the canonical based inverse. -/
@[simp]
theorem asEquivalence.inv
    (F : X ⟶ Y) [BasedFunctor.IsEquivalence F.hom] :
    (asEquivalence F).inv =
      Bicategory.InducedBicategory.mkHom F.hom.inv := rfl

/-- The forward morphism of `asEquivalenceOf` is the supplied owner morphism. -/
@[simp]
theorem asEquivalenceOf.hom
    (F : X ⟶ Y) (h : BasedFunctor.IsEquivalence F.hom) :
    (asEquivalenceOf F h).hom = F := rfl

/-- An owner morphism whose underlying based functor is an equivalence occurs as the forward
morphism of a bicategorical equivalence. -/
theorem exists_equivalence_of_isEquivalence
    (F : X ⟶ Y) [BasedFunctor.IsEquivalence F.hom] :
    ∃ e : X ≌ Y, e.hom = F := by
  exact ⟨Bicategory.Equivalence.mkOfAdjointifyCounit
    (f := F) (g := Bicategory.InducedBicategory.mkHom F.hom.inv)
    (Bicategory.InducedBicategory.isoMk F.hom.unitIso)
    (Bicategory.InducedBicategory.isoMk F.hom.counitIso), rfl⟩

/-- The underlying based functor of the forward morphism of a full-subbicategory equivalence is
an equivalence over the base. -/
theorem hom.isEquivalence
    (e : X ≌ Y) :
    BasedFunctor.IsEquivalence e.hom.hom :=
  ⟨⟨{
    inverse := e.inv.hom
    unitIso := Bicategory.InducedBicategory.forget.map₂Iso e.unit
    counitIso := Bicategory.InducedBicategory.forget.map₂Iso e.counit }⟩⟩

/-- The underlying based functor of the inverse morphism of a full-subbicategory equivalence is
an equivalence over the base. -/
theorem inv.isEquivalence
    (e : X ≌ Y) :
    BasedFunctor.IsEquivalence e.inv.hom :=
  ⟨⟨{
    inverse := e.hom.hom
    unitIso := (Bicategory.InducedBicategory.forget.map₂Iso e.counit).symm
    counitIso := (Bicategory.InducedBicategory.forget.map₂Iso e.unit).symm }⟩⟩

/-- Typeclass bridge from a full-subbicategory equivalence to its forward underlying based
functor. -/
instance homIsEquivalence
    (e : X ≌ Y) :
    BasedFunctor.IsEquivalence e.hom.hom := hom.isEquivalence e

/-- Typeclass bridge from a full-subbicategory equivalence to its inverse underlying based
functor. -/
instance invIsEquivalence
    (e : X ≌ Y) :
    BasedFunctor.IsEquivalence e.inv.hom := inv.isEquivalence e

end ObjectProperty.FullSubbicategory

end CategoryTheory
