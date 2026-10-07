module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Flasque
import StacksCheckRecall

universe u

/- Lemma 36.8.1: an injective quasicoherent module on a Noetherian scheme is flasque
as a sheaf of modules. -/
@[stacks 09T2] #check
  (AlgebraicGeometry.Scheme.QCoh.flasque_of_injective :
    {X : AlgebraicGeometry.Scheme.{u}} →
      [AlgebraicGeometry.IsNoetherian X] →
      (ℐ : AlgebraicGeometry.Scheme.QCoh X) →
      [CategoryTheory.Injective ℐ] →
      AlgebraicGeometry.RingedSpace.Modules.flasque X.toRingedSpace
        ((AlgebraicGeometry.Scheme.QCoh.inclusion X).obj ℐ))
