/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 35.14.5 (1): in a commutative triangle `f ≫ q = p`, smoothness descends from
`p` to `q` when `f` is surjective, flat, and locally of finite presentation. -/
@[stacks 05B5] #check
  (AlgebraicGeometry.Smooth.of_comp_eq_of_fppf :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
      [AlgebraicGeometry.Surjective f] [AlgebraicGeometry.Flat f]
      [AlgebraicGeometry.LocallyOfFinitePresentation f]
      [AlgebraicGeometry.Smooth p]
      (_ : f ≫ q = p),
      AlgebraicGeometry.Smooth q)

/- Lemma 35.14.5 (2): in a commutative triangle `f ≫ q = p`, étaleness descends from
`p` to `q` when `f` is surjective, flat, and locally of finite presentation. -/
@[stacks 05B5] #check
  (AlgebraicGeometry.Etale.of_comp_eq_of_fppf :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
      [AlgebraicGeometry.Surjective f] [AlgebraicGeometry.Flat f]
      [AlgebraicGeometry.LocallyOfFinitePresentation f]
      [AlgebraicGeometry.Etale p]
      (_ : f ≫ q = p),
      AlgebraicGeometry.Etale q)
