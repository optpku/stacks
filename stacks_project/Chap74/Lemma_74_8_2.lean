module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FppfDescent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 74.8.2 (1): in a commutative triangle `f ≫ q = p` of algebraic spaces
over `S`, local finite presentation descends from `p` to `q` when `f` is
surjective, flat, and locally of finite presentation. -/
@[stacks 0AHC] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation.of_comp_eq_of_fppf :
    ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
      (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
      [AlgebraicGeometry.AlgebraicSpace.Surjective f]
      [AlgebraicGeometry.AlgebraicSpace.Flat f]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation p]
      (_ : f ≫ q = p),
      AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation q)

/- Lemma 74.8.2 (2): in a commutative triangle `f ≫ q = p` of algebraic spaces
over `S`, local finite type descends from `p` to `q` when `f` is surjective,
flat, and locally of finite presentation. -/
@[stacks 0AHC] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.of_comp_eq_of_fppf :
    ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
      (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
      [AlgebraicGeometry.AlgebraicSpace.Surjective f]
      [AlgebraicGeometry.AlgebraicSpace.Flat f]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType p]
      (_ : f ≫ q = p),
      AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType q)
