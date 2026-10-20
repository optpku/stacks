/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.Normalized
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Normalized.Moore
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical normalized quotient versus transported Moore cochains

This leaf compares the canonical cokernel of the `QInfty` image inclusion directly with the
transported normalized Moore complex.  It does not pass through the degreewise span or the
source-facing normalized quotient.

@stack 019I
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicTopology AlgebraicTopology.DoldKan

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject.DoldKan.degenerate.normalized.moore

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The transported Moore projection annihilates the canonical degenerate image. -/
@[reassoc, stacks 019I "canonical degenerate image vanishes in transported Moore cochains"]
theorem degenerate_ι_comp_π (U : CosimplicialObject A) :
    DoldKan.degenerate.ι U ≫ normalizedMooreCochainComplex.π U = 0 := sorry

/-- The comparison from transported Moore cochains to the canonical normalized quotient. -/
@[stacks 019I "transported Moore to canonical normalized quotient comparison"]
noncomputable def hom (U : CosimplicialObject A) :
    normalizedMooreCochainComplex U ⟶ DoldKan.degenerate.normalized.obj U :=
  normalizedMooreCochainComplex.ι U ≫ DoldKan.degenerate.normalized.π U

/-- The comparison from the canonical normalized quotient to transported Moore cochains. -/
@[stacks 019I "canonical normalized quotient to transported Moore comparison"]
noncomputable def inv (U : CosimplicialObject A) :
    DoldKan.degenerate.normalized.obj U ⟶ normalizedMooreCochainComplex U :=
  DoldKan.degenerate.normalized.desc U (normalizedMooreCochainComplex.π U)
    (degenerate_ι_comp_π U)

/-- Precomposing the inverse comparison recovers the transported Moore projection. -/
@[reassoc, stacks 019I "canonical normalized quotient to Moore projection formula"]
theorem π_comp_inv (U : CosimplicialObject A) :
    DoldKan.degenerate.normalized.π U ≫ inv U =
      normalizedMooreCochainComplex.π U := sorry

/-- The Moore-to-quotient and quotient-to-Moore comparisons compose to the identity. -/
@[reassoc, stacks 019I "canonical Moore quotient comparison forward inverse law"]
theorem hom_comp_inv (U : CosimplicialObject A) : hom U ≫ inv U = 𝟙 _ := sorry

/-- The quotient-to-Moore and Moore-to-quotient comparisons compose to the identity. -/
@[reassoc, stacks 019I "canonical Moore quotient comparison inverse forward law"]
theorem inv_comp_hom (U : CosimplicialObject A) : inv U ≫ hom U = 𝟙 _ := sorry

/-- The canonical normalized quotient is objectwise isomorphic to transported Moore cochains. -/
@[stacks 019I "canonical normalized quotient transported Moore comparison"]
noncomputable def iso (U : CosimplicialObject A) :
    normalizedMooreCochainComplex U ≅ DoldKan.degenerate.normalized.obj U where
  hom := hom U
  inv := inv U
  hom_inv_id := hom_comp_inv U
  inv_hom_id := inv_comp_hom U

/-- The forward map of the canonical Moore comparison. -/
@[simp, stacks 019I "canonical Moore comparison forward map"]
theorem iso_hom (U : CosimplicialObject A) : (iso U).hom = hom U := sorry

/-- The inverse map of the canonical Moore comparison. -/
@[simp, stacks 019I "canonical Moore comparison inverse map"]
theorem iso_inv (U : CosimplicialObject A) : (iso U).inv = inv U := sorry

/-- The forward canonical Moore comparison is natural. -/
@[reassoc, stacks 019I "canonical Moore comparison forward naturality"]
theorem hom_naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    (normalizedMooreCochainComplex.functor (A := A)).map f ≫ hom V =
      hom U ≫ (DoldKan.degenerate.normalized.functor (A := A)).map f := sorry

/-- The inverse canonical Moore comparison is natural. -/
@[reassoc, stacks 019I "canonical Moore comparison inverse naturality"]
theorem inv_naturality {U V : CosimplicialObject A} (f : U ⟶ V) :
    (DoldKan.degenerate.normalized.functor (A := A)).map f ≫ inv V =
      inv U ≫ (normalizedMooreCochainComplex.functor (A := A)).map f := sorry

/-- The canonical Moore comparisons assemble into a natural isomorphism. -/
@[stacks 019I "canonical normalized quotient Moore natural comparison"]
noncomputable def natIso :
    normalizedMooreCochainComplex.functor (A := A) ≅
      DoldKan.degenerate.normalized.functor (A := A) :=
  NatIso.ofComponents (fun U ↦ iso U) (fun f ↦ hom_naturality f)

/-- The object component of the canonical Moore natural comparison. -/
@[simp, stacks 019I "canonical Moore natural comparison component"]
theorem natIso_app (U : CosimplicialObject A) :
    (natIso (A := A)).app U = iso U := sorry

namespace natIso

/-- The forward component of the canonical Moore natural comparison. -/
@[simp, stacks 019I "canonical Moore natural comparison forward component"]
theorem hom_app (U : CosimplicialObject A) :
    (natIso (A := A)).hom.app U = hom U := sorry

/-- The inverse component of the canonical Moore natural comparison. -/
@[simp, stacks 019I "canonical Moore natural comparison inverse component"]
theorem inv_app (U : CosimplicialObject A) :
    (natIso (A := A)).inv.app U = inv U := sorry

end natIso

end CategoryTheory.CosimplicialObject.DoldKan.degenerate.normalized.moore
