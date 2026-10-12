/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.Degenerate
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Split retracts for the canonical degenerate cochain image

The complementary Dold--Kan projector makes its canonical image inclusion a split monomorphism.
This leaf records the objectwise and natural split structures without importing the normalized
quotient of the image inclusion.

@stack 019I
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open AlgebraicTopology.DoldKan

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject.DoldKan.degenerate

variable {A : Type u} [Category.{v} A] [Preadditive A]
variable [hI : HasImages (ChainComplex Aᵒᵖ ℕ)]
  [hE : HasStrongEpiImages (ChainComplex Aᵒᵖ ℕ)]

include hI hE

/-- The canonical degenerate cochain inclusion followed by projection is the identity. -/
@[reassoc, stacks 019I "canonical degenerate cochain retract law"]
theorem ι_comp_ρ (U : CosimplicialObject A) :
    ι U ≫ ρ U = 𝟙 (obj U) := sorry

/-- The transported complementary projector is idempotent. -/
@[reassoc, stacks 019I "canonical degenerate projector idempotence"]
theorem projector_comp_projector (U : CosimplicialObject A) :
    projector U ≫ projector U = projector U := sorry

/-- The transported projector fixes the canonical degenerate inclusion. -/
@[reassoc, stacks 019I "canonical degenerate projector inclusion formula"]
theorem ι_comp_projector (U : CosimplicialObject A) :
    ι U ≫ projector U = ι U := sorry

/-- The canonical degenerate projection is unchanged after precomposition with the transported
projector. -/
@[reassoc, stacks 019I "canonical degenerate projector projection formula"]
theorem projector_comp_ρ (U : CosimplicialObject A) :
    projector U ≫ ρ U = ρ U := sorry

/-- The natural transported complementary projector is idempotent. -/
@[reassoc, stacks 019I "canonical degenerate natural projector idempotence"]
theorem projector.natTrans_comp_projector :
    projector.natTrans (A := A) ≫ projector.natTrans (A := A) =
      projector.natTrans (A := A) := sorry

/-- The natural degenerate inclusion is fixed by the transported projector. -/
@[reassoc, stacks 019I "canonical degenerate natural projector inclusion formula"]
theorem ι.natTrans_comp_projector :
    ι.natTrans (A := A) ≫ projector.natTrans (A := A) =
      ι.natTrans (A := A) := sorry

/-- The natural degenerate projection is unchanged after precomposition with the transported
projector. -/
@[reassoc, stacks 019I "canonical degenerate natural projector projection formula"]
theorem projector.natTrans_comp_ρ :
    projector.natTrans (A := A) ≫ ρ.natTrans (A := A) =
      ρ.natTrans (A := A) := sorry

/-- The canonical degenerate cochain retract is natural in the cosimplicial object. -/
@[reassoc, stacks 019I "canonical degenerate cochain natural retract law"]
theorem ι.natTrans_comp_ρ :
    ι.natTrans (A := A) ≫ ρ.natTrans (A := A) = 𝟙 degenerate.functor := sorry

namespace ι

/-- The natural canonical degenerate inclusion, equipped with its retraction. -/
@[stacks 019I "canonical degenerate cochain natural split monomorphism"]
noncomputable def splitMono : SplitMono (natTrans (A := A)) where
  retraction := ρ.natTrans (A := A)
  id := ι.natTrans_comp_ρ (A := A)

/-- The natural canonical degenerate inclusion is canonically split. -/
@[instance, stacks 019I "canonical degenerate cochain natural split monomorphism instance"]
theorem isSplitMono : IsSplitMono (natTrans (A := A)) := sorry

/-- A component of the canonical degenerate inclusion, equipped with its retraction. -/
@[stacks 019I "canonical degenerate cochain component split monomorphism"]
noncomputable def appSplitMono (U : CosimplicialObject A) :
    SplitMono (ι U) where
  retraction := ρ U
  id := ι_comp_ρ U

/-- Every component of the canonical degenerate inclusion is canonically split. -/
@[instance, stacks 019I "canonical degenerate cochain component split monomorphism instance"]
theorem appIsSplitMono (U : CosimplicialObject A) : IsSplitMono (ι U) := sorry

end ι

namespace ρ

/-- The natural canonical degenerate projection, equipped with its section. -/
@[stacks 019I "canonical degenerate cochain natural split epimorphism"]
noncomputable def splitEpi : SplitEpi (natTrans (A := A)) where
  section_ := ι.natTrans (A := A)
  id := ι.natTrans_comp_ρ (A := A)

/-- The natural canonical degenerate projection is canonically split. -/
@[instance, stacks 019I "canonical degenerate cochain natural split epimorphism instance"]
theorem isSplitEpi : IsSplitEpi (natTrans (A := A)) := sorry

/-- A component of the canonical degenerate projection, equipped with its section. -/
@[stacks 019I "canonical degenerate cochain component split epimorphism"]
noncomputable def appSplitEpi (U : CosimplicialObject A) :
    SplitEpi (ρ U) where
  section_ := ι U
  id := ι_comp_ρ U

/-- Every component of the canonical degenerate projection is canonically split. -/
@[instance, stacks 019I "canonical degenerate cochain component split epimorphism instance"]
theorem appIsSplitEpi (U : CosimplicialObject A) : IsSplitEpi (ρ U) := sorry

end ρ

end CategoryTheory.CosimplicialObject.DoldKan.degenerate
