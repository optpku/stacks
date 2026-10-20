module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient
import StacksCheckRecall

/-!
# Covering properties of groupoid quotients in algebraic spaces

If `(U, R, s, t, c)` is a groupoid in algebraic spaces whose source and target
are flat and locally of finite presentation, and `j = (t, s)` is an
equivalence relation, then a morphism `U ⟶ F` representing `F = U / R` is
surjective, flat, and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
universe u

/- Lemma 80.11.6: let `S` be a scheme. Consider an algebraic space `F` of
the form `F = U / R` where `(U, R, s, t, c)` is a groupoid in algebraic spaces
over `S` such that `s, t` are flat and locally of finite presentation, and
`j = (t, s) : R ⟶ U ⨯ U` is an equivalence relation. Then a morphism `q : U ⟶ F`
representing the quotient is surjective, flat, and locally of finite presentation. -/
@[stacks 06PG]
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.quotientHom_surjective_flat_locallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {F : AlgebraicSpace S} (q : G.U.left ⟶ F)
    (h_equalizes : G.toPreRelation.t.left ≫ q = G.toPreRelation.s.left ≫ q)
    [IsEquivalenceRelation G.t G.s]
    [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
    [AlgebraicSpace.LocallyOfFinitePresentation G.s.left]
    [AlgebraicSpace.LocallyOfFinitePresentation G.t.left]
    [IsIso (G.toPreRelation.quotientSheafDesc q h_equalizes)],
    AlgebraicSpace.Surjective q ∧ AlgebraicSpace.Flat q ∧
      AlgebraicSpace.LocallyOfFinitePresentation q)
