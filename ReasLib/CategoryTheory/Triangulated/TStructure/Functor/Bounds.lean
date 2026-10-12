/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# One-Sided Cohomological Bounds of Functors

This file owns the two independent one-sided bounds for functors between categories equipped
with t-structures.  The API is independent of derived functors, resolutions, and abelian
categories, so it can be reused for arbitrary pretriangulated categories.
-/

open CategoryTheory
open CategoryTheory.Limits

universe uC vC uD vD uE vE

namespace CategoryTheory.Functor.TStructure

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A functor maps every lower t-structure bound `a` to the shifted bound `a + p`. -/
def MapsGE (F : C ⥤ D) (tC : Triangulated.TStructure C)
    (tD : Triangulated.TStructure D) (p : ℤ) : Prop :=
  ∀ (X : C) (a : ℤ), tC.IsGE X a → tD.IsGE (F.obj X) (a + p)

namespace MapsGE

variable {F G : C ⥤ D}
variable {tC : Triangulated.TStructure C} {tD : Triangulated.TStructure D}
variable {p : ℤ}

/-- Apply a lower-bound preservation statement to one object and one degree. -/
theorem obj (h : MapsGE F tC tD p) (X : C) (a : ℤ) (hX : tC.IsGE X a) :
    tD.IsGE (F.obj X) (a + p) := sorry

/-- Preservation of lower bounds is invariant under a natural isomorphism of functors. -/
theorem ofIso (h : MapsGE F tC tD p) (e : F ≅ G) : MapsGE G tC tD p := sorry

/-- A lower-bound displacement may be decreased. -/
theorem mono {p' : ℤ} (h : MapsGE F tC tD p) (hp : p' ≤ p) :
    MapsGE F tC tD p' := sorry

/-- The identity functor preserves lower bounds without displacement. -/
theorem id : MapsGE (𝟭 C) tC tC 0 := sorry

variable {E : Type uE} [Category.{vE} E] [Preadditive E] [HasZeroObject E] [HasShift E ℤ]
  [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
variable {H : D ⥤ E} {tE : Triangulated.TStructure E} {r : ℤ}

/-- Lower-bound displacements add under composition. -/
theorem comp (hF : MapsGE F tC tD p) (hH : MapsGE H tD tE r) :
    MapsGE (F ⋙ H) tC tE (p + r) := sorry

end MapsGE

/-- A functor maps every upper t-structure bound `b` to the shifted bound `b + q`. -/
def MapsLE (F : C ⥤ D) (tC : Triangulated.TStructure C)
    (tD : Triangulated.TStructure D) (q : ℤ) : Prop :=
  ∀ (X : C) (b : ℤ), tC.IsLE X b → tD.IsLE (F.obj X) (b + q)

namespace MapsLE

variable {F G : C ⥤ D}
variable {tC : Triangulated.TStructure C} {tD : Triangulated.TStructure D}
variable {q : ℤ}

/-- Apply an upper-bound preservation statement to one object and one degree. -/
theorem obj (h : MapsLE F tC tD q) (X : C) (b : ℤ) (hX : tC.IsLE X b) :
    tD.IsLE (F.obj X) (b + q) := sorry

/-- Preservation of upper bounds is invariant under a natural isomorphism of functors. -/
theorem ofIso (h : MapsLE F tC tD q) (e : F ≅ G) : MapsLE G tC tD q := sorry

/-- An upper-bound displacement may be increased. -/
theorem mono {q' : ℤ} (h : MapsLE F tC tD q) (hq : q ≤ q') :
    MapsLE F tC tD q' := sorry

/-- The identity functor preserves upper bounds without displacement. -/
theorem id : MapsLE (𝟭 C) tC tC 0 := sorry

variable {E : Type uE} [Category.{vE} E] [Preadditive E] [HasZeroObject E] [HasShift E ℤ]
  [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
variable {H : D ⥤ E} {tE : Triangulated.TStructure E} {s : ℤ}

/-- Upper-bound displacements add under composition. -/
theorem comp (hF : MapsLE F tC tD q) (hH : MapsLE H tD tE s) :
    MapsLE (F ⋙ H) tC tE (q + s) := sorry

end MapsLE

end CategoryTheory.Functor.TStructure
