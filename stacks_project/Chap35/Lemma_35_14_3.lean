module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 35.14.3 (1): in a commutative triangle `f ≫ q = p`, local finite presentation
descends from `p` to `q` when `f` is surjective, flat, and locally of finite presentation. -/
@[stacks 02KL] #check
  (AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_eq_of_fppf :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
      [AlgebraicGeometry.Surjective f] [AlgebraicGeometry.Flat f]
      [AlgebraicGeometry.LocallyOfFinitePresentation f]
      [AlgebraicGeometry.LocallyOfFinitePresentation p]
      (_ : f ≫ q = p),
      AlgebraicGeometry.LocallyOfFinitePresentation q)

/- Lemma 35.14.3 (2): in a commutative triangle `f ≫ q = p`, local finite type descends
from `p` to `q` when `f` is surjective, flat, and locally of finite presentation. -/
@[stacks 02KL] #check
  (AlgebraicGeometry.LocallyOfFiniteType.of_comp_eq_of_fppf :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
      [AlgebraicGeometry.Surjective f] [AlgebraicGeometry.Flat f]
      [AlgebraicGeometry.LocallyOfFinitePresentation f]
      [AlgebraicGeometry.LocallyOfFiniteType p]
      (_ : f ≫ q = p),
      AlgebraicGeometry.LocallyOfFiniteType q)
