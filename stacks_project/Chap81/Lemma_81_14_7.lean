module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Compactification.ElementaryDistinguishedSquare
import StacksCheckRecall

/-!
# Lemma 81.14.7

Compactifications of the legs of an elementary distinguished square glue to a
compactification of the vertex, over a finite-type base over `ℤ`, when the
fibre product of the legs is dense in the vertex.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- Lemma 81.14.7. Let `B` be an algebraic space of finite type over `ℤ`. Let
`U` be an algebraic space of finite type and separated over `B`. Let
`(U2 ⊂ U, f : U1 → U)` be an elementary distinguished square. Assume `U1`
and `U2` have compactifications over `B` and `U1 ×_U U2 → U` has dense image.
Then `U` has a compactification over `B`. -/
@[stacks 0F4B] #check
  (AlgebraicGeometry.AlgebraicSpace.HasCompactification.of_isElementaryDistinguishedSquare :
    ∀ {B U U1 U2 : AlgebraicGeometry.AlgebraicSpace
        (AlgebraicGeometry.Spec (.of (ULift.{u} ℤ)))}
      [AlgebraicGeometry.AlgebraicSpace.FiniteType
        (AlgebraicGeometry.AlgebraicSpace.SchemeRealization.toBase B)]
      (fU : U ⟶ B)
      [AlgebraicGeometry.AlgebraicSpace.FiniteType fU]
      [AlgebraicGeometry.AlgebraicSpace.Separated fU]
      (j : U2 ⟶ U) (f : U1 ⟶ U)
      [AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare j f]
      [AlgebraicGeometry.AlgebraicSpace.HasCompactification (j ≫ fU)]
      [AlgebraicGeometry.AlgebraicSpace.HasCompactification (f ≫ fU)]
      (h_dense : Dense (Set.range
        (AlgebraicGeometry.AlgebraicSpace.Points.map
          (Limits.pullback.fst j f ≫ j))))
      , AlgebraicGeometry.AlgebraicSpace.HasCompactification fU)
