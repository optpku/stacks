module

public import Mathlib.CategoryTheory.Linear.LinearFunctor

@[expose] public section

universe uR uC vC uD vD

namespace CategoryTheory.Functor

variable (R : Type uR) [Semiring R]
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable [Preadditive C] [Preadditive D]
variable [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]

/-- A functor between preadditive `R`-linear categories is additive and scalar-compatible
if and only if it preserves every expression `r • f + g` on morphisms. -/
theorem additive_linear_iff_map_smul_add (F : C ⥤ D) :
    (F.Additive ∧ Functor.Linear R F) ↔
      ∀ (X Y : C) (r : R) (f g : X ⟶ Y),
        F.map (r • f + g) = r • F.map f + F.map g := sorry

end CategoryTheory.Functor
