module

public import stacks_project.Chap74.Lemma_74_8_5_Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 74.8.5 (1): in a commutative triangle `f ≫ q = p` of algebraic spaces
over `S`, if `f` is surjective, flat, and locally of finite presentation and `p`
is syntomic, then `q` is syntomic. -/
@[stacks 0AHF] #check
  (AlgebraicGeometry.AlgebraicSpace.Syntomic.of_comp_eq_of_fppf :
    ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
      (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
      [AlgebraicGeometry.AlgebraicSpace.Surjective f]
      [AlgebraicGeometry.AlgebraicSpace.Flat f]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f]
      [AlgebraicGeometry.AlgebraicSpace.Syntomic p]
      (_ : f ≫ q = p),
      AlgebraicGeometry.AlgebraicSpace.Syntomic q)

/- Lemma 74.8.5 (2): in a commutative triangle `f ≫ q = p` of algebraic spaces
over `S`, if `f` is surjective, flat, and locally of finite presentation and `p`
is syntomic, then `f` is syntomic. Here `Syntomic p` and `f ≫ q = p` identify
with `Syntomic (f ≫ q)`. -/
@[stacks 0AHF] #check
  (AlgebraicGeometry.AlgebraicSpace.Syntomic.left_of_comp_of_fppf :
    ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
      (f : X ⟶ Y) (q : Y ⟶ B)
      [AlgebraicGeometry.AlgebraicSpace.Surjective f]
      [AlgebraicGeometry.AlgebraicSpace.Flat f]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f],
      AlgebraicGeometry.AlgebraicSpace.Syntomic (f ≫ q) →
        AlgebraicGeometry.AlgebraicSpace.Syntomic f)
