module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Pair
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism.SchemeTheoreticImage

/-!
# Scheme-theoretic relation images of groupoid schemes

This module specializes the scheme-theoretic image construction to the canonical morphism
from a groupoid scheme to the pair groupoid on its object scheme.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- For the canonical map from a groupoid scheme to its pair groupoid, quasi-compactness
of the arrow map is equivalent to quasi-compactness of the arrow scheme. -/
theorem toPair_arrow_quasiCompact_iff
    {S : Scheme.{u}} {k : Type u} [Field k] (G : GroupoidScheme S)
    (eU : Spec (CommRingCat.of k) ≅ G.U.left) :
    QuasiCompact (toPair G).arrow.left ↔ CompactSpace G.R.left := sorry

/-- If the arrow scheme is compact, the canonical map `(t, s)` into the pair groupoid is
quasi-compact. -/
theorem toPair_arrow_quasiCompact
    {S : Scheme.{u}} {k : Type u} [Field k] (G : GroupoidScheme S)
    (eU : Spec (CommRingCat.of k) ≅ G.U.left) [CompactSpace G.R.left] :
    QuasiCompact (toPair G).arrow.left :=
  (toPair_arrow_quasiCompact_iff G eU).mpr inferInstance

/-- If the object scheme is the spectrum of a field and the arrow scheme is quasi-compact,
the scheme-theoretic image of `(t, s)` admits composition, identity, and inverse maps
satisfying the groupoid laws with the restricted pair-groupoid projections. -/
theorem relationImage
    {S : Scheme.{u}} {k : Type u} [Field k] (G : GroupoidScheme S)
    (eU : Spec (CommRingCat.of k) ≅ G.U.left) [CompactSpace G.R.left] :
    ∃ c e i,
      Hom.IsImageGroupoid (toPair G) c e i := by
  simpa using
    (@Hom.image _ _ _ _ _
      eU (toPair_object_eq G) (toPair G) (toPair_isIdentityOnObjects G)
      (toPair_arrow_quasiCompact G eU))

end AlgebraicGeometry.GroupoidScheme
