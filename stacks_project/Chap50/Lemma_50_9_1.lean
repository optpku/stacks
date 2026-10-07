module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.ChernClass.Pullback
import StacksCheckRecall

universe u

/- Lemma 50.9.1 (1): pullback along a commutative square of schemes commutes with the
de Rham first Chern class map. -/
@[stacks 0FMD] #check
  (AlgebraicGeometry.Scheme.DeRham.ChernClassContext.deRhamFirstChern_naturality :
    ∀ {X' X S' S : AlgebraicGeometry.Scheme.{u}}
      {f : X' ⟶ X} {h' : X' ⟶ S'} {h : X ⟶ S} {g : S' ⟶ S}
      (sq : CategoryTheory.CommSq f h' h g)
      (C : AlgebraicGeometry.Scheme.DeRham.ChernClassContext h)
      (C' : AlgebraicGeometry.Scheme.DeRham.ChernClassContext h')
      (P : AlgebraicGeometry.Scheme.DeRham.ChernClassContext.Pullback sq C C'),
      P.deRhamPullback.comp C.deRhamFirstChern =
        C'.deRhamFirstChern.comp (AlgebraicGeometry.Scheme.Hom.picardPullback f))

/- Lemma 50.9.1 (2): pullback along a commutative square of schemes commutes with the
Hodge first Chern class map. -/
@[stacks 0FMD] #check
  (AlgebraicGeometry.Scheme.DeRham.ChernClassContext.hodgeFirstChern_naturality :
    ∀ {X' X S' S : AlgebraicGeometry.Scheme.{u}}
      {f : X' ⟶ X} {h' : X' ⟶ S'} {h : X ⟶ S} {g : S' ⟶ S}
      (sq : CategoryTheory.CommSq f h' h g)
      (C : AlgebraicGeometry.Scheme.DeRham.ChernClassContext h)
      (C' : AlgebraicGeometry.Scheme.DeRham.ChernClassContext h')
      (P : AlgebraicGeometry.Scheme.DeRham.ChernClassContext.Pullback sq C C'),
      P.hodgePullback.comp C.hodgeFirstChern =
        C'.hodgeFirstChern.comp (AlgebraicGeometry.Scheme.Hom.picardPullback f))
