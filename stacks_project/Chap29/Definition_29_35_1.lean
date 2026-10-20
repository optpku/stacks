module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Local
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/- Definition 29.35.1 (1): unramifiedness at a point is witnessed on compatible affine source
and target neighborhoods. -/
@[stacks 02G4] #check
  (AlgebraicGeometry.Scheme.Hom.unramifiedAt_iff f x :
    f.UnramifiedAt x ↔
      ∃ V : S.affineOpens, ∃ U : X.affineOpens,
        x ∈ U.1 ∧ ∃ e : U.1 ≤ f ⁻¹ᵁ V.1,
          Unramified (f.resLE V.1 U.1 e))

/- Definition 29.35.1 (2): G-unramifiedness at a point is witnessed on compatible affine source
and target neighborhoods. -/
@[stacks 02G4] #check
  (AlgebraicGeometry.Scheme.Hom.gUnramifiedAt_iff f x :
    f.GUnramifiedAt x ↔
      ∃ V : S.affineOpens, ∃ U : X.affineOpens,
        x ∈ U.1 ∧ ∃ e : U.1 ≤ f ⁻¹ᵁ V.1,
          GUnramified (f.resLE V.1 U.1 e))

/- Definition 29.35.1 (3): a morphism is unramified exactly when it is unramified at every
source point. -/
@[stacks 02G4] #check
  (AlgebraicGeometry.Scheme.Hom.unramified_iff_forall_unramifiedAt f :
    Unramified f ↔ ∀ x : X, f.UnramifiedAt x)

/- Definition 29.35.1 (4): a morphism is G-unramified exactly when it is G-unramified at every
source point. -/
@[stacks 02G4] #check
  (AlgebraicGeometry.Scheme.Hom.gUnramified_iff_forall_gUnramifiedAt f :
    GUnramified f ↔ ∀ x : X, f.GUnramifiedAt x)

end AlgebraicGeometry
