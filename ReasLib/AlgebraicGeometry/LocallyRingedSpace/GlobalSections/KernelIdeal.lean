/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.GlobalSections.KernelIdeal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel ideals on locally ringed-space global sections

This is the locally ringed-space view of the ringed-space owner.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.Hom

/-- The global-sections kernel ideal of a morphism of locally ringed spaces to `Spec R`. -/
@[stacks 01IH "global-sections kernel ideal"]
noncomputable abbrev globalSectionsKernelIdeal
    {R : Type u} [CommRing R] {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace) : Ideal R :=
  RingedSpace.Hom.globalSectionsKernelIdeal i.toShHom

/-- Membership in the locally ringed-space global-sections kernel ideal is vanishing after
pullback to the source. -/
@[simp, stacks 01IH "global-sections kernel membership criterion"]
theorem mem_globalSectionsKernelIdeal_iff
    {R : Type u} [CommRing R] {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ (Spec (CommRingCat.of R)).toLocallyRingedSpace) (r : R) :
    r ∈ i.globalSectionsKernelIdeal ↔
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        LocallyRingedSpace.Γ.map i.op).hom r = 0 := sorry

end AlgebraicGeometry.LocallyRingedSpace.Hom
