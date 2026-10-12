/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.RingTheory.Localization.BasicOpen

/-!
# Sections on principal opens of an affine spectrum

The structure sheaf on `Spec R` identifies sections on `D(f)` with `R_f`.
This leaf records the concrete equivalence and its compatibility with
restriction between principal opens.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Spec.BasicOpen

/-- Lemma 26.5.4: sections of the structure sheaf on `D(f)` are the
localization `R_f`. -/
@[stacks 01HV]
noncomputable def sectionsIso {R : CommRingCat.{u}} (f : R) :
    Localization.Away f ≃ₐ[R] Γ(Spec R, PrimeSpectrum.basicOpen f) :=
  IsLocalization.algEquiv (.powers f) _ _

namespace SectionsIso

/-- The two scalar maps of the canonical principal-open sections isomorphism form an inverse
pair. This narrowly matching instance supports semilinear module comparisons. -/
@[stacks 01HV "principal-open sections scalar inverse pair"]
noncomputable instance homInvPair {R : CommRingCat.{u}} (f : R) :
    RingHomInvPair (sectionsIso f).toRingEquiv.toRingHom
      (sectionsIso f).symm.toRingEquiv.toRingHom :=
  RingHomInvPair.of_ringEquiv (sectionsIso f).toRingEquiv

/-- The inverse scalar map of the canonical principal-open sections isomorphism forms an inverse
pair with its forward map. -/
@[stacks 01HV "inverse principal-open sections scalar pair"]
noncomputable instance invHomInvPair {R : CommRingCat.{u}} (f : R) :
    RingHomInvPair (sectionsIso f).symm.toRingEquiv.toRingHom
      (sectionsIso f).toRingEquiv.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (sectionsIso f).toRingEquiv

end SectionsIso

/-- The principal-open sections equivalence carries the canonical localization map to the
structure-sheaf algebra map. -/
@[simp, stacks 01HV "principal-open sections scalar map"]
theorem sectionsIso_algebraMap {R : CommRingCat.{u}} (f r : R) :
    sectionsIso f (algebraMap R (Localization.Away f) r) =
      algebraMap R (Γ(Spec R, PrimeSpectrum.basicOpen f)) r := sorry

/-- Principal-open restriction agrees with the canonical localization map. -/
@[reassoc, stacks 01HV]
theorem sectionsIso_restriction {R : CommRingCat.{u}} {f g : R}
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    CommRingCat.ofHom (sectionsIso f).toRingHom ≫
        (Spec.structureSheaf R).1.map (homOfLE h).op =
      CommRingCat.ofHom (PrimeSpectrum.awayToAwayRingHom f g h) ≫
        CommRingCat.ofHom (sectionsIso g).toRingHom := sorry

end AlgebraicGeometry.Spec.BasicOpen
