module

public import stacks_project.Chap72.Lemma_72_4_2_Comparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 72.4.3: Let `S` be a scheme. Let `X` be an integral algebraic space over `S`.
The function field, or the field of rational functions of `X`, is the field `R(X)` of
Lemma 72.4.2, i.e. `RationalFunction X` / `rationalFunctionRing X`. -/
@[stacks 0ENE] #check
  (rationalFunctionRing :
    {S : Scheme.{u}} → AlgebraicSpace S → CommRingCat.{u + 1})

@[stacks 0ENE] #check
  (instField_rationalFunctionRing :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → [IsIntegral X] →
      Field (RationalFunction X))

#check RationalFunction
