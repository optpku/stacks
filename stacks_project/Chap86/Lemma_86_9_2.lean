module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RelativeDualizing.Homothety
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 86.9.2 (1): for a proper, flat, finitely presented morphism of algebraic spaces,
the canonical scalar homothety of any relative dualizing complex is an isomorphism. -/
@[stacks 0E5Y] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex.homothety_isIso :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
      [Proper f] [Flat f] [FinitePresentation f] (C : RelativeDualizingComplex f),
      IsIso (ModuleDerived.InternalHom.homothety C.complex))

/- Lemma 86.9.2 (2): for a proper, flat, finitely presented morphism of algebraic spaces,
the derived pushforward of any relative dualizing complex has vanishing cohomology sheaves
in every positive degree. -/
@[stacks 0E5Y] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex.pushforward_cohomology_isZero_of_pos :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
      [Proper f] [Flat f] [FinitePresentation f] (C : RelativeDualizingComplex f)
      (i : ℤ) (hi : 0 < i),
      IsZero (ModuleDerived.cohomologySheaf
        ((Modules.moduleDerivedPushforward f).obj C.complex) i))
