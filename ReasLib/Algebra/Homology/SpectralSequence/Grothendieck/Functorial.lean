/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Map.Total
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial families of Grothendieck spectral sequences

This leaf packages a coherent choice of realization at every bounded-below derived object and a
compatible realization map over every morphism.  Specializations should alias this owner instead
of repeating the identity and composition laws.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB wC v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Abelian A] [Abelian B] [Abelian C]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C] [HasInjectiveResolutions B]

/-- A coherent choice of Grothendieck spectral-sequence realizations, functorial in the
bounded-below derived input. -/
@[stacks 015N "functorial Grothendieck spectral sequence"]
structure Functorial (G : B ⥤ C) [G.Additive]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) where
  /-- The chosen realization at each bounded-below derived object. -/
  obj : (X : DerivedCategory.Plus A) → SpectralSequence G RF RGF X
  /-- The chosen realization map over each derived morphism. -/
  map : ∀ {X Y : DerivedCategory.Plus A} (f : X ⟶ Y), Map f (obj X) (obj Y)
  /-- The chosen maps preserve identities. -/
  map_id : ∀ X : DerivedCategory.Plus A, map (𝟙 X) = Map.id (obj X)
  /-- The chosen maps preserve composition. -/
  map_comp : ∀ {X Y Z : DerivedCategory.Plus A} (f : X ⟶ Y) (g : Y ⟶ Z),
    map (f ≫ g) = Map.comp (map f) (map g)

namespace Functorial

variable {G : B ⥤ C} [G.Additive]
variable {RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
variable {RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C}

/-- The total Grothendieck realization selected by a functorial family at one bounded-below
derived object. -/
@[stacks 015N "object selected by a functorial Grothendieck spectral sequence"]
noncomputable def toTotalObj (S : Functorial G RF RGF) (X : DerivedCategory.Plus A) :
    Total G RF RGF :=
  ⟨X, S.obj X⟩

/-- The total morphism selected by a functorial family over one bounded-below derived
morphism. -/
@[stacks 015N "map selected by a functorial Grothendieck spectral sequence"]
noncomputable def toTotalMap (S : Functorial G RF RGF)
    {X Y : DerivedCategory.Plus A} (f : X ⟶ Y) :
    toTotalObj S X ⟶ toTotalObj S Y :=
  ⟨f, S.map f⟩

/-- The selected total morphism over an identity is the identity. -/
@[stacks 015N "identity selected by a functorial Grothendieck spectral sequence"]
theorem toTotalMap_id (S : Functorial G RF RGF) (X : DerivedCategory.Plus A) :
    toTotalMap S (𝟙 X) = 𝟙 (toTotalObj S X) := sorry

/-- Selected total morphisms preserve composition. -/
@[stacks 015N "composition selected by a functorial Grothendieck spectral sequence"]
theorem toTotalMap_comp (S : Functorial G RF RGF)
    {X Y Z : DerivedCategory.Plus A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toTotalMap S (f ≫ g) = toTotalMap S f ≫ toTotalMap S g := sorry

/-- A functorial family of Grothendieck spectral sequences, regarded as a section of the total
category over bounded-below derived objects. -/
@[stacks 015N "functorial Grothendieck spectral sequence as a section of the total category"]
noncomputable def toTotalFunctor (S : Functorial G RF RGF) :
    DerivedCategory.Plus A ⥤ Total G RF RGF where
  obj X := toTotalObj S X
  map f := toTotalMap S f
  map_id := toTotalMap_id S
  map_comp := toTotalMap_comp S

/-- The base of the total realization selected at `X` is `X`. -/
@[simp, stacks 015N "base of a functorial Grothendieck spectral sequence"]
theorem toTotalFunctor_obj_base (S : Functorial G RF RGF) (X : DerivedCategory.Plus A) :
    (S.toTotalFunctor.obj X).base = X := sorry

/-- The realization selected by `toTotalFunctor` at `X` is the specified realization `S.obj X`. -/
@[simp, stacks 015N "realization of a functorial Grothendieck spectral sequence"]
theorem toTotalFunctor_obj_realization
    (S : Functorial G RF RGF) (X : DerivedCategory.Plus A) :
    (S.toTotalFunctor.obj X).realization = S.obj X := sorry

/-- The base component of the total morphism selected over `f` is `f`. -/
@[simp, stacks 015N "base map of a functorial Grothendieck spectral sequence"]
theorem toTotalFunctor_map_base (S : Functorial G RF RGF)
    {X Y : DerivedCategory.Plus A} (f : X ⟶ Y) :
    (S.toTotalFunctor.map f).base = f := sorry

/-- The realization component selected over `f` is the specified spectral-sequence map
`S.map f`. -/
@[simp, stacks 015N "realization map of a functorial Grothendieck spectral sequence"]
theorem toTotalFunctor_map_map (S : Functorial G RF RGF)
    {X Y : DerivedCategory.Plus A} (f : X ⟶ Y) :
    (S.toTotalFunctor.map f).map = S.map f := sorry

/-- Forgetting the selected total realizations recovers the identity functor on bounded-below
derived objects. -/
@[stacks 015N "base projection of a functorial Grothendieck spectral sequence"]
theorem toTotalFunctor_comp_forgetBase (S : Functorial G RF RGF) :
    S.toTotalFunctor ⋙ Total.forgetBase = 𝟭 (DerivedCategory.Plus A) := sorry

/- Axiom audit: the object and morphism maps of `toTotalFunctor` are explicit. Its `sorryAx`
dependency is confined to the separately named functor laws. -/

end Functorial

end CategoryTheory.Functor.RightDerived.Grothendieck.SpectralSequence
