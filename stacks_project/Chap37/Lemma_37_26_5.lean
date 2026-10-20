module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GeometricallyReduced.Constructible
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.26.5: for a quasi-compact morphism locally of finite presentation,
the locus in the target where the fibres are geometrically reduced is locally constructible. -/
@[stacks 0579] #check
  (AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_geometricallyReducedFiberLocus :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [LocallyOfFinitePresentation f],
      Topology.IsLocallyConstructible f.geometricallyReducedFiberLocus)

end AlgebraicGeometry.Scheme.Hom
