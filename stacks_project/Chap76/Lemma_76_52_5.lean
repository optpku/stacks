module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative.Tensor
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.DerivedCategory.DerivedTensor

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
          AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo f (K ⊗ᴸ M))
