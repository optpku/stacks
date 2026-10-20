module

public import ReasLib.AlgebraicGeometry.FormalScheme.Size

/-!
# Size of a formal scheme

The size counts formal affine opens and their rings of sections.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace Topology AlgebraicGeometry
open scoped Cardinal

namespace AlgebraicGeometry.FormalScheme

/- Lemma 87.2.1. The cardinal size of a formal scheme. -/
#check (AlgebraicGeometry.FormalScheme.IsAffineOpen :
    {X : FormalScheme.{u}} → Opens X.carrier → Prop)

#check (AlgebraicGeometry.FormalScheme.affineOpens :
    (X : FormalScheme.{u}) → Set (Opens X.carrier))

#check (AlgebraicGeometry.FormalScheme.mem_affineOpens :
    ∀ {X : FormalScheme.{u}} {U : Opens X.carrier},
      U ∈ X.affineOpens ↔ IsAffineOpen U)

#check (AlgebraicGeometry.FormalScheme.isAffineOpen_iff :
    ∀ {X : FormalScheme.{u}} {U : Opens X.carrier},
      IsAffineOpen U ↔
        ∃ (A : TopCommRingCat.{u}) (hA : TopologicalRing.IsAdmissibleRing A),
          Nonempty (X.toLocallyTopologicallyRingedSpace.restrict U.isOpenEmbedding ≅ spf A hA))

#check (AlgebraicGeometry.FormalScheme.size :
    FormalScheme.{u} → Cardinal.{u})

#check (AlgebraicGeometry.FormalScheme.size_eq :
    ∀ (X : FormalScheme.{u}),
      X.size = ℵ₀ ⊔ #X.affineOpens ⊔ ⨆ U : X.affineOpens, #(X.presheaf.obj (op U)))

#check (AlgebraicGeometry.FormalScheme.aleph0_le_size :
    ∀ (X : FormalScheme.{u}), ℵ₀ ≤ X.size)

#check (AlgebraicGeometry.FormalScheme.mk_affineOpens_le_size :
    ∀ (X : FormalScheme.{u}), #X.affineOpens ≤ X.size)

#check (AlgebraicGeometry.FormalScheme.mk_sections_le_size :
    ∀ (X : FormalScheme.{u}) (U : X.affineOpens),
      #(X.presheaf.obj (op U)) ≤ X.size)

end AlgebraicGeometry.FormalScheme
