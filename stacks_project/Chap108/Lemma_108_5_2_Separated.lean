/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import stacks_project.Chap108.Lemma_108_5_1_ClosedImmersion

/-!
# Separated functors on schemes over an algebraic space

A functor on `(Sch/B)ᵒᵖ` is separated over `B` when its product diagonal is a
closed immersion in the sense of `IsClosedImmersionOnSchemesOver`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- A functor on schemes over `B` is separated over `B` when its product
diagonal is a closed immersion. -/
class IsSeparatedOver (F : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)) : Prop where
  /-- The product diagonal is a closed immersion on schemes over `B`. -/
  isClosedImmersion_diagonal : IsClosedImmersionOnSchemesOver (Limits.diag F)

/-- A functor on schemes over `B` is separated over `B` if and only if its
product diagonal is a closed immersion. -/
theorem isSeparatedOver_iff (F : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)) :
    IsSeparatedOver F ↔ IsClosedImmersionOnSchemesOver (Limits.diag F) :=
  sorry

namespace IsSeparatedOver

/-- A functor on schemes over `B` whose product diagonal is a closed immersion
is separated over `B`. -/
theorem of {F : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)}
    (h : IsClosedImmersionOnSchemesOver (Limits.diag F)) :
    IsSeparatedOver F :=
  sorry

/-- The product diagonal of a functor separated over `B` is a closed immersion
on schemes over `B`. -/
theorem spec (F : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)) [IsSeparatedOver F] :
    IsClosedImmersionOnSchemesOver (Limits.diag F) :=
  sorry

end IsSeparatedOver

end AlgebraicGeometry.AlgebraicSpace.Quot
