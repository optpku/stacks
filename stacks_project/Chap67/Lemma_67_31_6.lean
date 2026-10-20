module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Open
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 67.31.6: A locally finitely presented morphism of algebraic spaces carrying a
finite-type quasi-coherent module of full support, flat over the target, is universally open. -/
@[stacks 0CVU] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.universallyOpen_of_flatOver_of_moduleSupport_eq_univ :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] [LocallyOfFinitePresentation f]
    (hsupp : moduleSupport F = Set.univ) (hflat : flatOver F f),
    UniversallyOpen f)
