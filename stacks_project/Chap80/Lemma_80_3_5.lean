module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Diagonal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- Lemma 80.3.5: if `S` is a scheme and `a : F ⟶ G` is a morphism of functors
`(Over S)ᵒᵖ ⥤ Type u` on `(Sch/S)_fppf` that is representable by algebraic spaces,
then the relative diagonal `Δ_{F/G} : F ⟶ F ×_G F`, given by
`pullback.diagonal a : F ⟶ pullback a a`, is representable by algebraic spaces. -/
@[stacks 05LA] #check
  (@AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.pullback_diagonal :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {F G : (CategoryTheory.Over S)ᵒᵖ ⥤ Type u}
      (a : F ⟶ G) (_ : CategoryTheory.Limits.HasPullback a a),
      AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces a →
        AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces
          (CategoryTheory.Limits.pullback.diagonal a))
