/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_8_3_Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 74.8.3 (1): in a commutative triangle `f ≫ q = p` of algebraic spaces
over `S`, syntomicity descends from `p` to `q` along a surjective syntomic
morphism `f`. -/
@[stacks 0AHD] #check
  (AlgebraicGeometry.AlgebraicSpace.Syntomic.of_comp_eq_of_surjective :
    ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
      (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
      [AlgebraicGeometry.AlgebraicSpace.Surjective f]
      [AlgebraicGeometry.AlgebraicSpace.Syntomic f]
      [AlgebraicGeometry.AlgebraicSpace.Syntomic p]
      (_ : f ≫ q = p),
      AlgebraicGeometry.AlgebraicSpace.Syntomic q)

/- Lemma 74.8.3 (2): in a commutative triangle `f ≫ q = p` of algebraic spaces
over `S`, smoothness descends from `p` to `q` along a surjective smooth
morphism `f`. -/
@[stacks 0AHD] #check
  (AlgebraicGeometry.AlgebraicSpace.Smooth.of_comp_eq_of_surjective :
    ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
      (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
      [AlgebraicGeometry.AlgebraicSpace.Surjective f]
      [AlgebraicGeometry.AlgebraicSpace.Smooth f]
      [AlgebraicGeometry.AlgebraicSpace.Smooth p]
      (_ : f ≫ q = p),
      AlgebraicGeometry.AlgebraicSpace.Smooth q)

/- Lemma 74.8.3 (3): in a commutative triangle `f ≫ q = p` of algebraic spaces
over `S`, étaleness descends from `p` to `q` along a surjective étale morphism
`f`. -/
@[stacks 0AHD] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.of_comp_eq_of_surjective :
    ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
      (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
      [AlgebraicGeometry.AlgebraicSpace.Surjective f]
      [AlgebraicGeometry.AlgebraicSpace.Etale f]
      [AlgebraicGeometry.AlgebraicSpace.Etale p]
      (_ : f ≫ q = p),
      AlgebraicGeometry.AlgebraicSpace.Etale q)
