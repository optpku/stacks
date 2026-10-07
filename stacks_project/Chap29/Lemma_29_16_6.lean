module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
import StacksCheckRecall

universe u

/- Lemma 29.16.6: a surjective locally finite type morphism maps the finite-type points of its
source onto the finite-type points of its target. -/
@[stacks 06EB] #check
  (AlgebraicGeometry.LocallyOfFiniteType.image_finiteTypePoints_eq_of_surjective :
    ∀ {T S : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.Surjective f],
      f '' AlgebraicGeometry.finiteTypePoints T = AlgebraicGeometry.finiteTypePoints S)
