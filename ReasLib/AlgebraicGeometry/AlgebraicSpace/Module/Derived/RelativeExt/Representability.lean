module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RelativeExt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.InternalHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-! # Pseudo-coherent representation of relative Ext -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- For a proper, flat, finitely presented morphism with quasi-compact, absolutely
quasi-separated target, relative Ext from a pseudo-coherent complex against a relatively
perfect complex has a pseudo-coherent representative. The same representative gives
the derived sheaf-Hom duality formula over the target and after every cartesian base change. -/
theorem existsPseudoCoherentRelativeExtRepresentation (f : X ⟶ Y)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [Proper f] [Flat f] [FinitePresentation f]
    (E K : ModuleDerived X) (hE : IsPerfectRelativeTo f E)
    (hK : IsPseudoCoherent X K) :
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
              ((DerivedCategory.singleFunctor (Modules Y') 0).obj (𝟙_ (Modules Y')))) := sorry

/-- Pseudo-coherent representatives of relative Ext from a pseudo-coherent complex
against a relatively perfect complex are isomorphic over a quasi-compact, absolutely
quasi-separated target of a proper, flat, finitely presented morphism. -/
theorem relativeExtRepresentation_unique (f : X ⟶ Y)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [Proper f] [Flat f] [FinitePresentation f]
    (E K : ModuleDerived X) (hE : IsPerfectRelativeTo f E)
    (hK : IsPseudoCoherent X K) (L L' : ModuleDerived Y)
    (hL : IsPseudoCoherent Y L) (hL' : IsPseudoCoherent Y L')
    (representsL : RepresentsRelativeExt f K E L)
    (representsL' : RepresentsRelativeExt f K E L') :
    IsIsomorphic L L' := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
