module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Abelian
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 39.14.6: if the source and target maps of a groupoid scheme are flat, then its
category of equivariant quasi-coherent modules is abelian. -/
@[stacks 077S]
#check (@AlgebraicGeometry.GroupoidScheme.QCoh.abelian :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
    [AlgebraicGeometry.Flat G.s.left] [AlgebraicGeometry.Flat G.t.left],
    CategoryTheory.Abelian G.QCoh)
