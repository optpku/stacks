/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Complex
import StacksCheckRecall

/-!
# Complexes and short exact sequences of first-order thickenings

The ideal-module complex condition determines a canonical trivialization of the first
thickening. Short exactness is short exactness of the reversed ideal-module row.
-/

open CategoryTheory
open scoped AlgebraicGeometry

universe u

section

open AlgebraicGeometry.RingedSpace.IsFirstOrderThickening

variable {X X₁ X₂ X₃ : AlgebraicGeometry.RingedSpace.{u}}
variable {i₁ : X ⟶ X₁} {i₂ : X ⟶ X₂} {i₃ : X ⟶ X₃}
variable [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening i₁]
variable [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening i₂]
variable [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening i₃]

/- Remark 91.4.9 (1) A sequence of first-order thickenings is a complex when the
induced ideal-module arrows ℐ₃ ⟶ ℐ₂ ⟶ ℐ₁ compose to zero. -/
@[stacks 08LE] #check (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.IsComplex :
  Hom i₁ i₂ → Hom i₂ i₃ → Prop)

#check (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.isComplex_iff :
  ∀ (f : Hom i₁ i₂) (g : Hom i₂ i₃), IsComplex f g ↔ g.idealMap ≫ f.idealMap = 0)

/- Remark 91.4.9 (2) A complex determines a canonical trivialization π : X₁ ⟶ X
of the first thickening, and the composite factors as π ≫ i₃. -/
@[stacks 08LE] #check
  (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.canonicalTrivialization :
    (f : Hom i₁ i₂) → (g : Hom i₂ i₃) → IsComplex f g → (X₁ ⟶ X))

#check (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.canonicalTrivialization_leftInv :
  ∀ (f : Hom i₁ i₂) (g : Hom i₂ i₃) (hC : IsComplex f g),
    i₁ ≫ canonicalTrivialization f g hC = 𝟙 X)
#check
  (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.comp_eq_canonicalTrivialization_comp_inclusion :
    ∀ (f : Hom i₁ i₂) (g : Hom i₂ i₃) (hC : IsComplex f g),
      f.hom ≫ g.hom = canonicalTrivialization f g hC ≫ i₃)

/- Remark 91.4.9 (3) A sequence of first-order thickenings is short exact when
the ideal-module row 0 ⟶ ℐ₃ ⟶ ℐ₂ ⟶ ℐ₁ ⟶ 0 is short exact. -/
@[stacks 08LE] #check (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.IsShortExact :
  Hom i₁ i₂ → Hom i₂ i₃ → Prop)

#check (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.isShortExact_iff :
  ∀ (f : Hom i₁ i₂) (g : Hom i₂ i₃),
    IsShortExact f g ↔ ∃ hC : IsComplex f g,
      (idealSheafShortComplex f g hC).Exact ∧ Mono g.idealMap ∧ Epi f.idealMap)

end
