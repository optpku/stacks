module

public import ReasLib.CategoryTheory.Homology.Homotopy.CochainShift
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {A B : CochainComplex C ℤ} (a b : A ⟶ B)

/- Lemma 12.14.9: self-homotopies of a cochain map `a : A ⟶ B` are canonically equivalent to
maps `A ⟶ B⟦-1⟧`. -/
#check (CochainComplex.Homotopy.selfEquivShiftHom a :
  Homotopy a a ≃ (A ⟶ B⟦(-1 : ℤ)⟧))

/- Lemma 12.14.9: homotopies between two cochain maps are either empty or form a principal
homogeneous space under the additive group of maps into the shifted target. -/
@[stacks 011I]
#check (CochainComplex.Homotopy.isEmpty_or_nonempty_addTorsor a b :
  IsEmpty (Homotopy a b) ∨ Nonempty (AddTorsor (A ⟶ B⟦(-1 : ℤ)⟧) (Homotopy a b)))
