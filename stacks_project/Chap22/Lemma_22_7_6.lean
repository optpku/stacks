module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible.HomotopyExact
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable {S₁ S₂ S₃ : ShortComplex (DifferentialGradedModule.{u, w} A)}
variable (hS₁ : IsAdmissibleShortExact S₁) (hS₂ : IsAdmissibleShortExact S₂)
variable (hS₃ : IsAdmissibleShortExact S₃)
variable {b : S₁.X₂ ⟶ S₂.X₂} {b' : S₂.X₂ ⟶ S₃.X₂}
variable (hf : Nonempty (Homotopy (S₁.f ≫ b) 0))
variable (hg : Nonempty (Homotopy (b ≫ S₂.g) 0))
variable (hf' : Nonempty (Homotopy (S₂.f ≫ b') 0))
variable (hg' : Nonempty (Homotopy (b' ≫ S₃.g) 0))

/- Lemma 22.7.6 (09JY): for three admissible short exact rows, homotopy commutativity of
the four zero-endpoint squares makes the composite of the two middle maps null-homotopic. -/
@[stacks 09JY] #check
  (ShortComplex.comp_nullHomotopic_of_rows hS₁ hS₂ hS₃ hf hg hf' hg' :
    Nonempty (Homotopy (b ≫ b') 0))

/- The reusable core needs only the admissible middle row and its two adjacent
null-homotopies. -/
#check @ShortComplex.comp_nullHomotopic_of_admissible
