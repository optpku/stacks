module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RelativeExt.Representability

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

noncomputable section

universe u

/- Remark 76.52.12 (1): the pseudo-coherent relative Ext representative also
satisfies derived duality over `Y` and after arbitrary cartesian base change. -/
@[stacks 0DKZ]
#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.existsPseudoCoherentRelativeExtRepresentation :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [Proper f] [Flat f] [FinitePresentation f]
    (E K : ModuleDerived X) (hE : IsPerfectRelativeTo f E)
    (hK : IsPseudoCoherent X K),
    ∃ L : ModuleDerived Y,
      IsPseudoCoherent Y L ∧ RepresentsRelativeExt f K E L ∧
      IsIsomorphic ((Modules.moduleDerivedPushforward f).obj (InternalHom.obj K E))
        (InternalHom.obj L ((DerivedCategory.singleFunctor (Modules Y) 0).obj
          (𝟙_ (Modules Y)))) ∧
      ∀ {X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y),
        IsPullback g' f' f g →
          IsIsomorphic
            ((Modules.moduleDerivedPushforward f').obj
              (InternalHom.obj ((ModuleDerived.pullback g').obj K)
                ((ModuleDerived.pullback g').obj E)))
            (InternalHom.obj ((ModuleDerived.pullback g).obj L)
              ((DerivedCategory.singleFunctor (Modules Y') 0).obj (𝟙_ (Modules Y')))))

/- Remark 76.52.12 (2): any two pseudo-coherent representatives of the relative Ext
functor are isomorphic in the derived category of modules on `Y`. -/
@[stacks 0DKZ]
#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.relativeExtRepresentation_unique :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [Proper f] [Flat f] [FinitePresentation f]
    (E K : ModuleDerived X) (hE : IsPerfectRelativeTo f E)
    (hK : IsPseudoCoherent X K) (L L' : ModuleDerived Y)
    (hL : IsPseudoCoherent Y L) (hL' : IsPseudoCoherent Y L')
    (representsL : RepresentsRelativeExt f K E L)
    (representsL' : RepresentsRelativeExt f K E L'),
    IsIsomorphic L L')
