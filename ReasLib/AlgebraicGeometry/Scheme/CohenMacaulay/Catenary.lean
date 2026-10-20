module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.Locality
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Locality
public import ReasLib.RingTheory.CohenMacaulay.Catenary

/-!
# Universal catenarity of Cohen-Macaulay schemes

This module records the universal catenarity of Cohen-Macaulay schemes.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Every Cohen-Macaulay scheme is universally catenary. -/
instance instUniversallyCatenaryOfCohenMacaulay (S : Scheme.{u}) [Scheme.CohenMacaulay S] :
    UniversallyCatenary S := by
  rw [UniversallyCatenary.iff_forall_affineOpen]
  intro U
  exact universallyCatenaryRing_of_cohenMacaulayRing
    ((Scheme.cohenMacaulay_iff_forall_affineOpen_sectionsRing_cohenMacaulayRing S).1
      inferInstance U)

end AlgebraicGeometry
