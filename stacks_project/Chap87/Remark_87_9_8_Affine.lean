module

public import ReasLib.AlgebraicGeometry.FormalScheme.Affine
public import ReasLib.AlgebraicGeometry.FormalScheme.Scheme
import StacksCheckRecall

/-!
# Affine EGA formal schemes

An EGA formal scheme is affine when its underlying locally topologically ringed space
is isomorphic to an admissible formal spectrum.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace Topology AlgebraicGeometry
open scoped Cardinal

namespace AlgebraicGeometry.FormalScheme

/- Remark 87.9.8. Affine EGA formal schemes. -/
@[stacks 0AIE] #check (AlgebraicGeometry.FormalScheme.ofSpf :
    (A : TopCommRingCat.{u}) →
      TopologicalRing.IsAdmissibleRing A → FormalScheme.{u})

#check (AlgebraicGeometry.FormalScheme.ofSpf_toLocallyTopologicallyRingedSpace :
    ∀ (A : TopCommRingCat.{u})
      (hA : TopologicalRing.IsAdmissibleRing A),
      (ofSpf A hA).toLocallyTopologicallyRingedSpace = spf A hA)

#check (AlgebraicGeometry.FormalScheme.IsAffine :
    FormalScheme.{u} → Prop)

#check (AlgebraicGeometry.FormalScheme.IsAffine.of :
    ∀ {X : FormalScheme.{u}} {A : TopCommRingCat.{u}}
      (hA : TopologicalRing.IsAdmissibleRing A),
      Nonempty (X.toLocallyTopologicallyRingedSpace ≅ spf A hA) → IsAffine X)

#check (AlgebraicGeometry.FormalScheme.IsAffine.spec :
    ∀ (X : FormalScheme.{u}) [IsAffine X],
      ∃ (A : TopCommRingCat.{u}) (hA : TopologicalRing.IsAdmissibleRing A),
        Nonempty (X.toLocallyTopologicallyRingedSpace ≅ spf A hA))

#check (AlgebraicGeometry.FormalScheme.IsAffine.iff :
    ∀ (X : FormalScheme.{u}),
      IsAffine X ↔
        ∃ (A : TopCommRingCat.{u}) (hA : TopologicalRing.IsAdmissibleRing A),
          Nonempty (X.toLocallyTopologicallyRingedSpace ≅ spf A hA))

#check (AlgebraicGeometry.FormalScheme.instIsAffine_ofSpf :
    ∀ (A : TopCommRingCat.{u})
      (hA : TopologicalRing.IsAdmissibleRing A), IsAffine (ofSpf A hA))

end AlgebraicGeometry.FormalScheme
