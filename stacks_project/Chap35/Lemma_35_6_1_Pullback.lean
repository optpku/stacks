module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback

open CategoryTheory

universe u

/- The reusable quasi-coherent pullback functor remains available through this
source compatibility module. -/
#check
  (AlgebraicGeometry.Scheme.QCoh.pullback :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}}, (Y ⟶ X) →
      AlgebraicGeometry.Scheme.QCoh X ⥤ AlgebraicGeometry.Scheme.QCoh Y)
