/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_52_5_Tensor
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.52.5 (1): for a scheme `S` and a flat, locally finitely presented morphism
`f : X ⟶ Y` of algebraic spaces over `S`, every perfect object of `D(𝒪_X)` is `Y`-perfect. -/
@[stacks 0DKS] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect.isPerfectRelativeTo :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Flat f] [LocallyOfFinitePresentation f]
      {K : ModuleDerived X},
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect K →
        AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo f K)

/- Lemma 76.52.5 (2): for a scheme `S` and a flat, locally finitely presented morphism
`f : X ⟶ Y` of algebraic spaces over `S`, tensoring a perfect object by a `Y`-perfect
object preserves `Y`-perfectness. -/
@[stacks 0DKS] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect.tensor_isPerfectRelativeTo :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Flat f] [LocallyOfFinitePresentation f]
      {K M : ModuleDerived X},
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect K →
        AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo f M →
          AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo f
            (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.tensorObj K M))
