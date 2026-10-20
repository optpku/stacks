module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 65.6.2: a scheme is an algebraic space. More precisely, given a scheme `S` and
`T` in `Ob((Sch/S)_fppf)`, the representable functor `h_T`, identified with `yoneda.obj T`
on `Over S`, is an algebraic space over `S`. -/
@[stacks 025Z] #check (AlgebraicGeometry.AlgebraicSpace.ofOver :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    CategoryTheory.Over S → AlgebraicGeometry.AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.ofOver_functorOfPoints :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (T : CategoryTheory.Over S),
    (AlgebraicGeometry.AlgebraicSpace.ofOver T).functorOfPoints =
      CategoryTheory.yoneda.obj T)
