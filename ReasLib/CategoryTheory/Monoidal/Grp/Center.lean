/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory.GrpObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {T G : C} [GrpObj G]

/-- A generalized point is central when its commutator with the universal second point is
constantly the unit. -/
def IsCentral (g : T ⟶ G) : Prop :=
  lift (fst T G ≫ g) (snd T G) ≫ commutator G = toUnit (T ⊗ G) ≫ η[G]

/-- A generalized point is central exactly when all its base changes commute with all points. -/
theorem isCentral_iff (g : T ⟶ G) :
    IsCentral g ↔ ∀ (U : C) (f : U ⟶ T) (x : U ⟶ G),
      (f ≫ g) * x = x * (f ≫ g) := sorry

/-- Centrality of a generalized point is preserved by precomposition. -/
theorem IsCentral.comp {g : T ⟶ G} (hg : IsCentral g) {U : C} (f : U ⟶ T) :
    IsCentral (f ≫ g) := sorry

end CategoryTheory.GrpObj
