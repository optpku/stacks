/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Comparison.Transpose
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory

open MonoidalCategory
open scoped CategoryTheory.RightInternalHom

variable {C : Type u} [Category.{v} C]

section Monoidal

variable [MonoidalCategory C]
variable (H H' : RightInternalHom C) (X Y Z : C)

/- Remark 4.43.12: a chosen right internal-Hom structure represents
`Mor(W ⊗ X, Y)` by `Mor(W, hom(X, Y))`, naturally in all three variables. -/
@[stacks 0GWJ "right internal-Hom data"]
#check (RightInternalHom C : Type (max u v))

/- The representing bifunctor is unique up to the canonical natural isomorphism of right
adjoints. -/
@[stacks 0GWJ "uniqueness of the right internal-Hom bifunctor"]
#check (RightInternalHom.uniqueIso H H' : H.hom ≅ H'.hom)

/- Remark 4.43.12 (1): evaluation for a right internal Hom. -/
@[stacks 0GWJ "evaluation for a right internal Hom"]
#check (RightInternalHom.ev H X Y : (X ⟶[H]ᵣ Y) ⊗ X ⟶ Y)

/- Remark 4.43.12 (2): composition of right internal-Hom morphisms. -/
@[stacks 0GWJ "composition of right internal-Hom morphisms"]
#check (RightInternalHom.comp H X Y Z :
  (Y ⟶[H]ᵣ Z) ⊗ (X ⟶[H]ᵣ Y) ⟶ (X ⟶[H]ᵣ Z))

/- Remark 4.43.12 (3): left tensoring of a right internal-Hom morphism. -/
@[stacks 0GWJ "left tensoring of a right internal-Hom morphism"]
#check (RightInternalHom.tensorLeft H X Y Z :
  Z ⊗ (X ⟶[H]ᵣ Y) ⟶ (X ⟶[H]ᵣ (Z ⊗ Y)))

/- Remark 4.43.12 (4): coevaluation for a right internal Hom. -/
@[stacks 0GWJ "coevaluation for a right internal Hom"]
#check (RightInternalHom.coev H X Y : Y ⟶ (X ⟶[H]ᵣ (Y ⊗ X)))

end Monoidal

section Symmetric

variable [MonoidalCategory C] [SymmetricCategory C]
variable (H : RightInternalHom C) (X Y Z : C)

/- Remark 4.43.12 (5): the interchange map between right internal Homs in a symmetric monoidal
category. -/
@[stacks 0GWJ "symmetric interchange map between right internal Homs"]
#check (RightInternalHom.compTranspose H X Y Z :
  (Y ⟶[H]ᵣ Z) ⊗ X ⟶ ((X ⟶[H]ᵣ Y) ⟶[H]ᵣ Z))

end Symmetric

end CategoryTheory
