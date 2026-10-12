/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.UniverseLift
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Sheafification

/-!
# Successor-universe sheafification on small commutative scheme sites

Relative differentials of a commutative small-étale ringed morphism need
`HasSheafCompose` for `forget₂ CommRingCat RingCat` on the small standard
sites, together with identity local-bijectivity facts for sheafification.
Weak sheafification and `WEqualsLocallyBijective` at `AddCommGrpCat.{u + 1}`
are reused from `StandardTopology.Small.instCommHasWeakSheafify`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The small standard topology supports composition with `forget₂` into rings in
the successor universe. -/
instance smallStandard_hasSheafCompose_commRing
    (τ : StandardTopology) (S : Scheme.{u}) :
    (StandardTopology.Small.topology τ S).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := sorry

/-- Identities of ring-valued sheaves on a small standard site are locally
injective in the successor universe. -/
instance (priority := high) smallStandard_id_isLocallyInjective
    (τ : StandardTopology) (S : Scheme.{u})
    (R : Sheaf (StandardTopology.Small.topology τ S) RingCat.{u + 1}) :
    Presheaf.IsLocallyInjective (StandardTopology.Small.topology τ S) (𝟙 R.obj) :=
  sorry

/-- Identities of ring-valued sheaves on a small standard site are locally
surjective in the successor universe. -/
instance (priority := high) smallStandard_id_isLocallySurjective
    (τ : StandardTopology) (S : Scheme.{u})
    (R : Sheaf (StandardTopology.Small.topology τ S) RingCat.{u + 1}) :
    Presheaf.IsLocallySurjective (StandardTopology.Small.topology τ S) (𝟙 R.obj) :=
  sorry

/-- The identity of a lifted commutative small-standard structure sheaf is
locally injective. -/
instance (priority := high) smallCommRingedSite_structureSheaf_id_isLocallyInjective
    (τ : StandardTopology) (S : Scheme.{u}) :
    Presheaf.IsLocallyInjective
      (smallCommRingedSite τ S).siteTopology
      (𝟙 (smallCommRingedSite τ S).structureSheaf.obj) :=
  sorry

/-- The identity of a lifted commutative small-standard structure sheaf is
locally surjective. -/
instance (priority := high) smallCommRingedSite_structureSheaf_id_isLocallySurjective
    (τ : StandardTopology) (S : Scheme.{u}) :
    Presheaf.IsLocallySurjective
      (smallCommRingedSite τ S).siteTopology
      (𝟙 (smallCommRingedSite τ S).structureSheaf.obj) :=
  sorry

end AlgebraicGeometry.Scheme
