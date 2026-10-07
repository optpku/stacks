module

public import ReasLib.CategoryTheory.Idempotents.Preadditive
import StacksCheckRecall

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

/- Lemma 12.4.2 [09SH]: the shared owner records the three source clauses as a typed TFAE,
while its component theorems remain directly usable without list-index reasoning. -/
@[stacks 09SH]
#check (CategoryTheory.Idempotents.karoubian_tfae (C := C) :
  List.TFAE
    [ IsIdempotentComplete C
    , ∀ (Z : C) (p : Z ⟶ Z), p ≫ p = p → HasCokernel p
    , ∀ (Z : C) (p : Z ⟶ Z), p ≫ p = p →
        ∃ (X Y : C) (_ : HasBinaryBiproduct X Y) (e : X ⊞ Y ≅ Z),
          p = e.inv ≫ biprod.snd ≫ biprod.inr ≫ e.hom
    ])

#check @CategoryTheory.Idempotents.isIdempotentComplete_iff_idempotents_have_cokernels
#check @CategoryTheory.Idempotents.idempotentIsSecondSummandProjection
