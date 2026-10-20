/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.Linear
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Verdier Quotients of Triangulated Object Properties

This leaf owns the canonical localization model of the Verdier quotient by a triangulated
object property. The quotient notation is only a view of `verdierQuotient`; downstream code can
also use the named quotient functor and its automatically available additive, linear, and
triangulated structure.
-/

universe v u

namespace CategoryTheory.ObjectProperty

open CategoryTheory Limits MorphismProperty Pretriangulated
open scoped CategoryTheory.ObjectProperty

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Stacks 05RI: the Verdier quotient by `P` is the localization at its cone-defined
morphism property. -/
@[stacks 05RI]
abbrev verdierQuotient (P : ObjectProperty D) : Type u :=
  P.trW.Localization

/-- Stacks 05RI: the canonical functor to the Verdier quotient by `P`. -/
@[stacks 05RI]
abbrev verdierQuotientFunctor (P : ObjectProperty D) : D ⥤ verdierQuotient P :=
  P.trW.Q

/-- Stacks 05RI: scoped notation `D / P` denotes the Verdier quotient by `P`. -/
@[stacks 05RI]
scoped instance verdierQuotientHDiv : HDiv (Type u) (ObjectProperty D) (Type u) where
  hDiv _ P := verdierQuotient P

/-- The Verdier quotient inherits the category structure of its localization model. -/
@[stacks 05RI]
scoped instance verdierQuotientCategory (P : ObjectProperty D) : Category (D / P) :=
  inferInstanceAs (Category (verdierQuotient P))

namespace VerdierQuotient

/-- Stacks 05RI: the quotient functor localizes at the cone-defined Verdier system. -/
@[stacks 05RI]
instance functorIsLocalization (P : ObjectProperty D) :
    (P.trW.Q : D ⥤ D / P).IsLocalization P.trW :=
  Functor.q_isLocalization P.trW

end VerdierQuotient

section

variable [IsTriangulated D] (P : ObjectProperty D) [P.IsTriangulated]

namespace VerdierQuotient

/-- The Verdier quotient is preadditive. -/
@[stacks 05RI]
noncomputable instance preadditive : Preadditive (D / P) :=
  by
    change Preadditive P.trW.Localization
    infer_instance

/-- The quotient functor is additive. -/
@[stacks 05RI]
noncomputable instance functorAdditive : (P.trW.Q : D ⥤ D / P).Additive :=
  inferInstance

/-- The Verdier quotient has a zero object. -/
@[stacks 05RI]
noncomputable instance hasZeroObject : HasZeroObject (D / P) :=
  by
    change HasZeroObject P.trW.Localization
    infer_instance

/-- The Verdier quotient has the localization-induced shift. -/
@[stacks 05RI]
noncomputable instance hasShift : HasShift (D / P) ℤ :=
  by
    change HasShift P.trW.Localization ℤ
    infer_instance

/-- The quotient functor commutes with the canonical shifts. -/
@[stacks 05RI]
noncomputable instance functorCommShift :
    (P.trW.Q : D ⥤ D / P).CommShift ℤ :=
  inferInstance

/-- Every shift functor on a Verdier quotient is additive. -/
@[stacks 05RI]
noncomputable instance shiftAdditive (n : ℤ) :
    (shiftFunctor (D / P) n).Additive :=
  by
    change (shiftFunctor P.trW.Localization n).Additive
    infer_instance

/-- The bundled family of shift-additivity instances required by triangulated APIs. -/
@[stacks 05RI]
noncomputable instance shiftsAdditive :
    ∀ n : ℤ, (shiftFunctor (D / P) n).Additive :=
  fun n => shiftAdditive P n

/-- The localization-induced pretriangulated structure on a Verdier quotient. -/
@[stacks 05RI]
noncomputable instance pretriangulated : Pretriangulated (D / P) :=
  by
    change Pretriangulated P.trW.Localization
    infer_instance

/-- The quotient functor is triangulated. -/
@[stacks 05RI]
noncomputable instance functorTriangulated :
    (P.trW.Q : D ⥤ D / P).IsTriangulated :=
  inferInstance

/-- The localization-induced triangulated structure on a Verdier quotient. -/
@[stacks 05RI]
noncomputable instance triangulated : IsTriangulated (D / P) :=
  by
    change IsTriangulated P.trW.Localization
    infer_instance


end VerdierQuotient

end

end CategoryTheory.ObjectProperty
