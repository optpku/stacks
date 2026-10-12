/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.StructureSheaf

/-!
# Stalks of affine spectra

This file records support instances for the canonical equivalence between a localization at a
prime and the corresponding structure-sheaf stalk. Keeping these instances with the ring
equivalence lets semilinear downstream APIs use it without importing module-specific tilde theory.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.StructureSheaf.StalkIso

/-- The scalar maps of the canonical affine stalk isomorphism form an inverse pair. -/
noncomputable instance homInvPair {R : CommRingCat.{u}} (x : PrimeSpectrum R) :
    RingHomInvPair (StructureSheaf.stalkIso R x).toRingEquiv.toRingHom
      (StructureSheaf.stalkIso R x).symm.toRingEquiv.toRingHom :=
  RingHomInvPair.of_ringEquiv (StructureSheaf.stalkIso R x).toRingEquiv

/-- The inverse scalar map of the canonical affine stalk isomorphism forms an inverse pair with
its forward map. -/
noncomputable instance invHomInvPair {R : CommRingCat.{u}} (x : PrimeSpectrum R) :
    RingHomInvPair (StructureSheaf.stalkIso R x).symm.toRingEquiv.toRingHom
      (StructureSheaf.stalkIso R x).toRingEquiv.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (StructureSheaf.stalkIso R x).toRingEquiv

end AlgebraicGeometry.StructureSheaf.StalkIso
