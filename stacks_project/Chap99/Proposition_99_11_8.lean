module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative.Representability

/-!
# Proposition 99.11.8

If `f : X ⟶ B` is a flat, finitely presented, proper morphism of algebraic
spaces over a scheme `S`, and `O_T ⟶ f_{T,*} O_{X_T}` is an isomorphism for
every scheme `T` over `B`, then the Picard functor `Pic_{X/B}` is an algebraic
space.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Proposition 99.11.8: let `S` be a scheme and let `f : X ⟶ B` be a morphism
of algebraic spaces over `S`. If `f` is flat, of finite presentation, and
proper, and `O_T ⟶ f_{T,*} O_{X_T}` is an isomorphism for every scheme `T`
over `B`, then `picardFunctor f` (`Pic_{X/B}`) is an algebraic space. -/
@[stacks 0D2C] #check
  (AlgebraicGeometry.AlgebraicSpace.picardFunctor_isAlgebraicSpaceOver :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [Flat f] [FinitePresentation f] [Proper f]
      [Hom.IsIsoBaseChangeStructurePushforward f],
      IsAlgebraicSpaceOver (picardFunctor f).obj)
