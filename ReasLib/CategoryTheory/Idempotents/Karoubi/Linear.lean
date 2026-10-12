/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.CategoryTheory.Linear.Basic

@[expose] public section

open CategoryTheory

universe w v u

namespace CategoryTheory.Idempotents.Karoubi

variable {R : Type w} [Semiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
variable {P Q : Karoubi C}

/-- Scalar multiplication of Karoubi morphisms is inherited from their underlying morphisms. -/
instance instSMulHom : SMul R (P ⟶ Q) where
  smul r f :=
    { f := r • f.f
      comm := sorry }

/-- The underlying morphism of a scalar multiple in the Karoubi envelope. -/
@[simp]
theorem smul_f (r : R) (f : P ⟶ Q) : (r • f).f = r • f.f := sorry

/-- Every Hom group in a Karoubi envelope inherits the ambient module structure. -/
instance instModuleHom : Module R (P ⟶ Q) :=
  Function.Injective.module R (inclusionHom P Q) sorry sorry

/-- The Karoubi envelope of an `R`-linear category is canonically `R`-linear. -/
instance instLinear : Linear R (Karoubi C) where
  homModule := fun _ _ ↦ instModuleHom
  smul_comp := sorry
  comp_smul := sorry

end CategoryTheory.Idempotents.Karoubi
