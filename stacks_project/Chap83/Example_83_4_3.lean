module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.CategoricalQuotient
import stacks_project.Chap66.Definition_66_3_1_Separation
import stacks_project.Chap68.Lemma_68_12_8_Decent
import stacks_project.Chap66.Lemma_66_13_1_IsScheme
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace ObjectProperty

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
variable (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U)
variable (φ : U ⟶ X)

/- Example 83.4.3 (1): if `C` is the category of all algebraic spaces over `B`, a
categorical quotient in `C` is a categorical quotient. -/
@[stacks 049V] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotientIn P ⊤ φ : Prop)

section
variable [IsAbsolutelySeparated B]

/- Example 83.4.3 (2): if `B` is separated and `C` is the category of all separated
algebraic spaces over `B`, a categorical quotient in `C` is a categorical quotient in
separated algebraic spaces. -/
@[stacks 049V] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotientIn P
    (fun Y => IsAbsolutelySeparated Y.left) φ : Prop)

end

section
variable [IsAbsolutelyQuasiSeparated B]

/- Example 83.4.3 (3): if `B` is quasi-separated and `C` is the category of all
quasi-separated algebraic spaces over `B`, a categorical quotient in `C` is a
categorical quotient in quasi-separated algebraic spaces. -/
@[stacks 049V] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotientIn P
    (fun Y => IsAbsolutelyQuasiSeparated Y.left) φ : Prop)

end

section
variable [IsAbsolutelyLocallySeparated B]

/- Example 83.4.3 (4): if `B` is locally separated and `C` is the category of all
locally separated algebraic spaces over `B`, a categorical quotient in `C` is a
categorical quotient in locally separated algebraic spaces. -/
@[stacks 049V] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotientIn P
    (fun Y => IsAbsolutelyLocallySeparated Y.left) φ : Prop)

end

section
variable [IsDecent B]

/- Example 83.4.3 (5): if `B` is decent and `C` is the category of all decent algebraic
spaces over `B`, a categorical quotient in `C` is a categorical quotient in decent
algebraic spaces. -/
@[stacks 049V] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotientIn P
    (fun Y => IsDecent Y.left) φ : Prop)

end

variable {U₀ X₀ : Over (AlgebraicGeometry.AlgebraicSpace.ofOver (Over.mk (𝟙 S)))}
variable (P₀ : AlgebraicGeometry.AlgebraicSpace.PreRelation U₀)
variable (φ₀ : U₀ ⟶ X₀)

/- Example 83.4.3 (6): if `B = S` and `C` is the category of schemes over `S`, a
categorical quotient in `C` is a categorical quotient in schemes. -/
@[stacks 049V] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotientIn P₀
    (fun Y => IsScheme Y.left) φ₀ : Prop)
