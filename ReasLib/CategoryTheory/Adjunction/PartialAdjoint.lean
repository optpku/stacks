/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import ReasLib.CategoryTheory.ObjectProperty.Cover
import Mathlib.Tactic.CrossRefAttribute

/-!
# Partial adjoints from quotient-generating object properties

This module extends mathlib's partial-left-adjoint API. In a category in which every
epimorphism is regular, an object property with epimorphic covers detects whether the partial
left adjoint is defined everywhere.
-/

@[expose] public section

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [HasColimitsOfShape WalkingParallelPair A]
variable {B : Type u₂} [Category.{v₂} B] [IsRegularEpiCategory B]

/-- An epimorphically covering object property on which the partial left adjoint is defined
forces its domain of definition to contain every object. -/
@[stacks 0793 "partial left adjoint defined on an epimorphically covering property"]
theorem leftAdjointObjIsDefined_eq_top_of_hasEpiCover
    (u : A ⥤ B) (P : ObjectProperty B) [P.HasEpiCover]
    (hdefined : P ≤ u.leftAdjointObjIsDefined) :
    u.leftAdjointObjIsDefined = ⊤ := sorry

/-- A functor admits a left adjoint when its partial left adjoint is defined on an object
property that epimorphically covers every object. -/
@[stacks 0793 "right adjoint criterion from an epimorphically covering property"]
theorem isRightAdjoint_of_hasEpiCover
    (u : A ⥤ B) (P : ObjectProperty B) [P.HasEpiCover]
    (hdefined : P ≤ u.leftAdjointObjIsDefined) :
    u.IsRightAdjoint := sorry

end CategoryTheory.Functor
