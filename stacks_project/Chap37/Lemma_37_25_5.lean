module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.Constructible
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.25.5: for a finite-presentation morphism `f : X ⟶ Y`, a finitely
presented quasi-coherent module ℱ on `X`, and an open `U ⊆ X` whose composite
`U.ι ≫ f` is quasi-compact, the locus of `y : Y` where the associated points
of the restriction of ℱ to the fiber over `y` lie in the fiber of `U` is locally
constructible. -/
@[stacks 05KR] #check
  (AlgebraicGeometry.Scheme.Hom.associatedPoints_fiber_subset_isLocallyConstructible :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Scheme.Hom.FinitePresentation f]
      (ℱ : X.Modules) [ℱ.IsFinitePresentation] (U : X.Opens) [QuasiCompact (U.ι ≫ f)],
      Topology.IsLocallyConstructible
        {y : Y | ((Scheme.Modules.pullback (f.fiberι y)).obj ℱ).associatedPoints ⊆
          (f.fiberι y) ⁻¹' (U : Set X)})

end AlgebraicGeometry.Scheme.Hom
