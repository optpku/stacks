module

public import stacks_project.Chap76.Lemma_76_15_4
public import stacks_project.Chap76.Definition_76_6_5_Conormal
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

noncomputable section

variable {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S}
variable (h : Z ⟶ X) [FormallyUnramified h]
variable (i : Z ⟶ Z') (f : Z' ⟶ X) [IsUniversalFirstOrder i f]

/- Definition 76.15.5 (1): Let `S` be a scheme. Let `h : Z ⟶ X` be a formally
unramified morphism of algebraic spaces over `S`. The universal first-order
thickening of `Z` over `X` is the thickening `Z ⊂ Z'` constructed in
Lemma 76.15.4. -/
@[stacks 0607]
#check
  (IsUniversalFirstOrder.exists_of_formallyUnramified h :
    ∃ (Z' : AlgebraicSpace S) (i : Z ⟶ Z') (f : Z' ⟶ X),
      i ≫ f = h ∧ IsUniversalFirstOrder i f)

/- Definition 76.15.5 (2): The conormal sheaf of `Z` over `X`, often denoted
`C_{Z/X}`, is the conormal sheaf of `Z` in its universal first-order thickening
`Z'` over `X`. -/
@[stacks 0607]
#check (Hom.conormalSheaf i : Z.Modules)
