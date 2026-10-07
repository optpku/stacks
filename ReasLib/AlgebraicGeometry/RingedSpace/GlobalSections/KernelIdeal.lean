module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel ideals on global sections

This file owns the ringed-space construction.  Affine closed-immersion and
scheme-facing APIs specialize it without rebuilding the comparison with
global sections of an affine scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

/-- The ideal of `R` killed on global sections by a morphism to `Spec R`. -/
@[stacks 01IN "global-sections kernel ideal"]
noncomputable def globalSectionsKernelIdeal
    {R : Type u} [CommRing R] {Z : RingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace.toRingedSpace) :
    Ideal R :=
  RingHom.ker
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      SheafedSpace.Γ.map i.op).hom

/-- Membership in the global-sections kernel ideal means that the corresponding affine global
section restricts to zero on the source. -/
@[simp]
theorem mem_globalSectionsKernelIdeal_iff
    {R : Type u} [CommRing R] {Z : RingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace.toRingedSpace) (r : R) :
    r ∈ globalSectionsKernelIdeal i ↔
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        SheafedSpace.Γ.map i.op).hom r = 0 := sorry

end AlgebraicGeometry.RingedSpace.Hom
