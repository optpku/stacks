module

public import stacks_project.Chap74.Lemma_74_8_4_Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 74.8.4 (1): in a commutative triangle `f ≫ q = p` of algebraic spaces
over `S`, smoothness descends from `p` to `q` when `f` is surjective, flat, and
locally of finite presentation. -/
@[stacks 0AHE] #check
  (AlgebraicGeometry.AlgebraicSpace.Smooth.of_comp_eq_of_fppf :
    ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
      (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
      [AlgebraicGeometry.AlgebraicSpace.Surjective f]
      [AlgebraicGeometry.AlgebraicSpace.Flat f]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f]
      [AlgebraicGeometry.AlgebraicSpace.Smooth p]
      (_ : f ≫ q = p),
      AlgebraicGeometry.AlgebraicSpace.Smooth q)

/- Lemma 74.8.4 (2): in a commutative triangle `f ≫ q = p` of algebraic spaces
over `S`, étaleness descends from `p` to `q` when `f` is surjective, flat, and
locally of finite presentation. -/
@[stacks 0AHE] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.of_comp_eq_of_fppf :
    ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
      (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
      [AlgebraicGeometry.AlgebraicSpace.Surjective f]
      [AlgebraicGeometry.AlgebraicSpace.Flat f]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f]
      [AlgebraicGeometry.AlgebraicSpace.Etale p]
      (_ : f ≫ q = p),
      AlgebraicGeometry.AlgebraicSpace.Etale q)
