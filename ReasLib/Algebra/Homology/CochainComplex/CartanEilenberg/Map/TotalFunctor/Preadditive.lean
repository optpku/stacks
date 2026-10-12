/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Total.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.TotalFunctor

/-!
# Additive total functors of Cartan--Eilenberg resolutions

The raw, bounded-below, mapped, and filtered total functors carry canonical additive structures.
Keeping these instances in a dedicated leaf makes additive downstream constructions inferable
without local `letI` declarations.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]

/-- The raw total functor on bundled Cartan--Eilenberg resolutions is additive. -/
@[stacks 015J "additivity of the raw Cartan-Eilenberg total functor"]
noncomputable instance total_additive :
    (total : Bundled A ⥤ CochainComplex A ℤ).Additive := sorry

/-- The bounded-below total functor on bundled resolutions is additive. -/
@[stacks 015J "additivity of the bounded-below Cartan-Eilenberg total functor"]
noncomputable instance totalPlus_additive :
    (totalPlus : Bundled A ⥤ CochainComplex.Plus A).Additive := sorry

section Mapped

variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- Termwise application followed by totalization is additive on resolution morphisms. -/
@[stacks 015J "additivity of mapped Cartan-Eilenberg totalization"]
noncomputable instance mappedTotal_additive (F : A ⥤ B) [F.Additive] :
    (mappedTotal F).Additive := sorry

namespace First

/-- The first filtered-total functor is additive. -/
@[stacks 015J "additivity of the first filtered Cartan-Eilenberg total functor"]
noncomputable instance filteredTotal_additive (F : A ⥤ B) [F.Additive] :
    (filteredTotal F).Additive := sorry

end First

namespace Second

/-- The second filtered-total functor is additive. -/
@[stacks 015J "additivity of the second filtered Cartan-Eilenberg total functor"]
noncomputable instance filteredTotal_additive (F : A ⥤ B) [F.Additive] :
    (filteredTotal F).Additive := sorry

end Second

end Mapped

#synth (total : Bundled A ⥤ CochainComplex A ℤ).Additive
#synth (totalPlus : Bundled A ⥤ CochainComplex.Plus A).Additive

end CochainComplex.CartanEilenbergResolution.Bundled
