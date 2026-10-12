/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import ReasLib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.LinearAlgebra.Isomorphisms
public import ReasLib.CategoryTheory.Filtration.GradedPiece
public import ReasLib.Order.Filtration
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtrations on Cohomology Modules

This file gives the explicit `ModuleCat` model of the filtration induced on the cohomology of a
two-step complex.  The categorical owner for arbitrary filtered complexes remains
`FilteredComplex.inducedCohomologyFiltration`; this leaf supplies the reusable kernel/range
quotient presentation and the linear equivalences needed by module-valued consumers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uR uPrev uMid uNext

noncomputable section

namespace ModuleCat

variable {R : Type uR} [Ring R]

namespace FilteredCohomology

variable {KPrev : Type uPrev} [AddCommGroup KPrev] [Module R KPrev]
variable {K : Type uMid} [AddCommGroup K] [Module R K]
variable {KNext : Type uNext} [AddCommGroup KNext] [Module R KNext]

/-- The boundary submodule lies in the cycle submodule for a two-step complex. -/
theorem boundaries_le_cycles (dPrev : KPrev →ₗ[R] K) (dNext : K →ₗ[R] KNext)
    (hcomp : dNext.comp dPrev = 0) : dPrev.range ≤ dNext.ker := sorry

/-- The boundary submodule, regarded as a submodule of cycles. -/
noncomputable abbrev boundariesInCycles (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (hcomp : dNext.comp dPrev = 0) :
    Submodule R dNext.ker :=
  LinearMap.range <|
    LinearMap.codRestrict dNext.ker dPrev fun x ↦
      boundaries_le_cycles dPrev dNext hcomp (LinearMap.mem_range_self dPrev x)

/-- The cohomology module `ker dNext / range dPrev` of a two-step complex. -/
abbrev cohomology (dPrev : KPrev →ₗ[R] K) (dNext : K →ₗ[R] KNext)
    (hcomp : dNext.comp dPrev = 0) :=
  dNext.ker ⧸ boundariesInCycles dPrev dNext hcomp

namespace Stage

/-- The representative `(ker dNext ∩ F p) + range dPrev` of the induced filtration stage. -/
abbrev representative (dPrev : KPrev →ₗ[R] K) (dNext : K →ₗ[R] KNext)
    (F : ℤ → Submodule R K) (p : ℤ) : Submodule R K :=
  Order.Filtration.Subquotient.representative F dPrev.range dNext.ker p

/-- The quotient presentation of the `p`-th induced cohomology-filtration stage. -/
@[stacks 012R]
abbrev step (dPrev : KPrev →ₗ[R] K) (dNext : K →ₗ[R] KNext)
    (F : ℤ → Submodule R K) (p : ℤ) :=
  ↥(representative dPrev dNext F p) ⧸
    dPrev.range.submoduleOf (representative dPrev dNext F p)

/-- The representative submodules decrease whenever the original filtration decreases. -/
theorem representative_mono (dPrev : KPrev →ₗ[R] K) (dNext : K →ₗ[R] KNext)
    (F : ℤ → Submodule R K) {p q : ℤ} (hpq : F q ≤ F p) :
    representative dPrev dNext F q ≤ representative dPrev dNext F p := sorry

/-- The quotient of filtered cycles by filtered boundaries. -/
abbrev cyclesQuotient (dPrev : KPrev →ₗ[R] K) (dNext : K →ₗ[R] KNext)
    (F : ℤ → Submodule R K) (p : ℤ) :=
  ↥(dNext.ker ⊓ F p) ⧸
    (dPrev.range ⊓ F p).submoduleOf (dNext.ker ⊓ F p)

/-- The denominator used by the second isomorphism law is the filtered boundary submodule. -/
theorem cyclesDenominator_eq (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K) (p : ℤ) :
    Submodule.comap (Submodule.subtype (dNext.ker ⊓ F p)) (dNext.ker ⊓ F p) ⊓
        Submodule.comap (Submodule.subtype (dNext.ker ⊓ F p)) dPrev.range =
      (dPrev.range ⊓ F p).submoduleOf (dNext.ker ⊓ F p) := sorry

/-- The second isomorphism law identifies filtered cycles modulo filtered boundaries with the
source-facing representative quotient. -/
noncomputable def cyclesQuotientEquiv (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K) (p : ℤ) :
    (↥(dNext.ker ⊓ F p) ⧸ (dPrev.range ⊓ F p).submoduleOf (dNext.ker ⊓ F p)) ≃ₗ[R]
      step dPrev dNext F p := by
  rw [← cyclesDenominator_eq dPrev dNext F p]
  change
    _ ≃ₗ[R]
      (↥(dNext.ker ⊓ F p ⊔ dPrev.range) ⧸
        dPrev.range.submoduleOf (dNext.ker ⊓ F p ⊔ dPrev.range))
  simpa [Submodule.submoduleOf, sup_comm] using
    LinearMap.quotientInfEquivSupQuotient (dNext.ker ⊓ F p) dPrev.range

/-- The canonical map from filtered cycles to the ambient cohomology module. -/
noncomputable abbrev stageMap (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (p : ℤ) :
    ↥(dNext.ker ⊓ F p) →ₗ[R] cohomology dPrev dNext hcomp :=
  (boundariesInCycles dPrev dNext hcomp).mkQ.comp
    (Submodule.inclusion (show dNext.ker ⊓ F p ≤ dNext.ker from inf_le_left))

/-- The `p`-th induced filtration stage as a submodule of cohomology. -/
noncomputable def stageSubmodule (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (p : ℤ) :
    Submodule R (cohomology dPrev dNext hcomp) :=
  LinearMap.range (stageMap dPrev dNext F hcomp p)

/-- Pointwise inclusion of middle filtration stages induces inclusion of cohomology stages. -/
theorem stageSubmodule_mono (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) {p q : ℤ} (hpq : F q ≤ F p) :
    stageSubmodule dPrev dNext F hcomp q ≤ stageSubmodule dPrev dNext F hcomp p := sorry

/-- An antitone middle filtration induces an antitone family of cohomology stages. -/
theorem stageSubmodule_antitone (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) :
    Antitone (stageSubmodule dPrev dNext F hcomp) := sorry

/-- The subobjects corresponding to the cohomology stages are monotone in the dual index. -/
theorem induced_monotone (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) :
    Monotone (fun p : ℤᵒᵈ ↦
      (subobjectModule (of R (cohomology dPrev dNext hcomp))).symm
        (stageSubmodule dPrev dNext F hcomp (OrderDual.ofDual p))) := sorry

/-- The decreasing filtration induced on `ker dNext / range dPrev`. -/
@[stacks 012R]
noncomputable def induced (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) :
    CategoryTheory.DecreasingFiltration (of R (cohomology dPrev dNext hcomp)) where
  toFun p := (subobjectModule (of R (cohomology dPrev dNext hcomp))).symm
    (stageSubmodule dPrev dNext F hcomp (OrderDual.ofDual p))
  monotone' := induced_monotone dPrev dNext F hcomp hF

/-- The submodule represented by an induced filtration stage is the corresponding stage image. -/
theorem induced_stage (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) (p : ℤ) :
    subobjectModule (of R (cohomology dPrev dNext hcomp))
        ((induced dPrev dNext F hcomp hF).stage p) =
      stageSubmodule dPrev dNext F hcomp p := sorry

/-- The kernel of the stage map is the filtered boundary submodule. -/
theorem ker_stageMap (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (p : ℤ) :
    LinearMap.ker (stageMap dPrev dNext F hcomp p) =
      (dPrev.range ⊓ F p).submoduleOf (dNext.ker ⊓ F p) := sorry

/-- Filtered cycles modulo filtered boundaries identify with the image defining the cohomology
stage. -/
noncomputable def cyclesQuotientEquivStage (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (p : ℤ) :
    cyclesQuotient dPrev dNext F p ≃ₗ[R] stageSubmodule dPrev dNext F hcomp p :=
  (Submodule.quotEquivOfEq _ _ (ker_stageMap dPrev dNext F hcomp p).symm).trans
    (stageMap dPrev dNext F hcomp p).quotKerEquivRange

/-- The textbook quotient-step presentation identifies with the intrinsic stage submodule. -/
noncomputable def stepEquiv (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (p : ℤ) :
    step dPrev dNext F p ≃ₗ[R] stageSubmodule dPrev dNext F hcomp p :=
  (cyclesQuotientEquiv dPrev dNext F p).symm.trans
    (cyclesQuotientEquivStage dPrev dNext F hcomp p)

/-- Equation `(12.24.5.1)`: the representative quotient is canonically the underlying module of
the corresponding induced filtration stage. -/
@[stacks 012R]
noncomputable def stepEquivFiltration (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) (p : ℤ) :
    step dPrev dNext F p ≃ₗ[R]
      subobjectModule (of R (cohomology dPrev dNext hcomp))
        ((induced dPrev dNext F hcomp hF).stage p) :=
  (stepEquiv dPrev dNext F hcomp p).trans
    (LinearEquiv.ofEq _ _ (induced_stage dPrev dNext F hcomp hF p).symm)

end Stage

/-! ## Graded pieces -/

namespace GradedPiece

/-- The numerator in the textbook presentation of an induced cohomology graded piece. -/
abbrev representative (dNext : K →ₗ[R] KNext)
    (F : ℤ → Submodule R K) (p : ℤ) : Submodule R K :=
  dNext.ker ⊓ F p

/-- The denominator in the textbook presentation of an induced cohomology graded piece. -/
abbrev denominator (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K) (p : ℤ) :
    Submodule R (representative dNext F p) :=
  (dNext.ker ⊓ F (p + 1)).submoduleOf (representative dNext F p) ⊔
    (dPrev.range ⊓ F p).submoduleOf (representative dNext F p)

namespace Presentation

/-- The explicit quotient presentation of the `p`-th induced cohomology graded piece. -/
abbrev quotient (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K) (p : ℤ) :=
  ↥(representative dNext F p) ⧸ denominator dPrev dNext F p

end Presentation

end GradedPiece

namespace Stage

/-- Consecutive induced cohomology stages are nested. -/
theorem submodule_succ_le (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) (p : ℤ) :
    stageSubmodule dPrev dNext F hcomp (p + 1) ≤
      stageSubmodule dPrev dNext F hcomp p := sorry

/-- The quotient of one induced cohomology stage by the next stage. -/
abbrev quotient (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (p : ℤ) :=
  ↥(stageSubmodule dPrev dNext F hcomp p) ⧸
    (stageSubmodule dPrev dNext F hcomp (p + 1)).submoduleOf
      (stageSubmodule dPrev dNext F hcomp p)

/-- The categorical filtration stage is canonically the module carried by its explicit stage
submodule. -/
noncomputable def filtrationIso (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) (p : ℤ) :
    ((induced dPrev dNext F hcomp hF).stage p : ModuleCat R) ≅
      of R ↥(stageSubmodule dPrev dNext F hcomp p) :=
  ModuleCat.SubobjectModule.underlyingIso
    (of R (cohomology dPrev dNext hcomp))
    (stageSubmodule dPrev dNext F hcomp p)

/-- The explicit inclusion of the next induced cohomology stage into the current one. -/
noncomputable def inclusion (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) (p : ℤ) :
    of R ↥(stageSubmodule dPrev dNext F hcomp (p + 1)) ⟶
      of R ↥(stageSubmodule dPrev dNext F hcomp p) :=
  ofHom (Submodule.inclusion (submodule_succ_le dPrev dNext F hcomp hF p))

/-- The abstract filtration inclusion agrees with the explicit submodule inclusion. -/
theorem filtration_naturality (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) (p : ℤ) :
    (induced dPrev dNext F hcomp hF).succInclusion p ≫
        (filtrationIso dPrev dNext F hcomp hF p).hom =
      (filtrationIso dPrev dNext F hcomp hF (p + 1)).hom ≫
        inclusion dPrev dNext F hcomp hF p := sorry

/-- The categorical graded piece is canonically the cokernel of the explicit stage inclusion. -/
noncomputable def gradedPieceIso (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) (p : ℤ) :
    (induced dPrev dNext F hcomp hF).gradedPiece p ≅
      cokernel (inclusion dPrev dNext F hcomp hF p) :=
  cokernel.mapIso
    ((induced dPrev dNext F hcomp hF).succInclusion p)
    (inclusion dPrev dNext F hcomp hF p)
    (filtrationIso dPrev dNext F hcomp hF (p + 1))
    (filtrationIso dPrev dNext F hcomp hF p)
    (filtration_naturality dPrev dNext F hcomp hF p)

/-- The range of the explicit stage inclusion is the next stage viewed inside the current one. -/
theorem inclusion_range (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) (p : ℤ) :
    LinearMap.range (inclusion dPrev dNext F hcomp hF p).hom =
      (stageSubmodule dPrev dNext F hcomp (p + 1)).submoduleOf
        (stageSubmodule dPrev dNext F hcomp p) := sorry

end Stage

namespace GradedPiece

/-- The categorical graded piece is canonically the quotient of consecutive explicit stages. -/
noncomputable def equivStage (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) (p : ℤ) :
    (Stage.induced dPrev dNext F hcomp hF).gradedPiece p ≃ₗ[R]
      Stage.quotient dPrev dNext F hcomp p :=
  (Stage.gradedPieceIso dPrev dNext F hcomp hF p).toLinearEquiv.trans <|
    (cokernelIsoRangeQuotient
      (Stage.inclusion dPrev dNext F hcomp hF p)).toLinearEquiv.trans <|
      Submodule.quotEquivOfEq _ _
        (Stage.inclusion_range dPrev dNext F hcomp hF p)

/-- The filtered-cycle map with codomain restricted to its intrinsic cohomology stage. -/
noncomputable def representativeToStage (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (p : ℤ) :
    ↥(representative dNext F p) →ₗ[R]
      Stage.stageSubmodule dPrev dNext F hcomp p :=
  LinearMap.codRestrict _ (Stage.stageMap dPrev dNext F hcomp p)
    (LinearMap.mem_range_self (Stage.stageMap dPrev dNext F hcomp p))

/-- The canonical map from filtered-cycle representatives to the quotient of consecutive
cohomology stages. -/
noncomputable def representativeToQuotient (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (p : ℤ) :
    ↥(representative dNext F p) →ₗ[R]
      Stage.quotient dPrev dNext F hcomp p :=
  ((Stage.stageSubmodule dPrev dNext F hcomp (p + 1)).submoduleOf
    (Stage.stageSubmodule dPrev dNext F hcomp p)).mkQ.comp
      (representativeToStage dPrev dNext F hcomp p)

/-- The textbook denominator is killed by the map to the quotient of consecutive stages. -/
theorem denominator_le_ker (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) (p : ℤ) :
    denominator dPrev dNext F p ≤
      LinearMap.ker (representativeToQuotient dPrev dNext F hcomp p) := sorry

namespace Presentation

/-- The canonical comparison from the explicit graded-piece quotient to the quotient of
consecutive induced cohomology stages. -/
noncomputable def toQuotient (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) (p : ℤ) :
    Presentation.quotient dPrev dNext F p →ₗ[R]
      Stage.quotient dPrev dNext F hcomp p :=
  (denominator dPrev dNext F p).liftQ
    (representativeToQuotient dPrev dNext F hcomp p)
    (denominator_le_ker dPrev dNext F hcomp hF p)

/-- The comparison from the explicit graded-piece quotient to the quotient of consecutive
stages is bijective; this is the combined second and third isomorphism law. -/
theorem toQuotient_bijective (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) (p : ℤ) :
    Function.Bijective (toQuotient dPrev dNext F hcomp hF p) := sorry

/-- The explicit graded-piece quotient is canonically equivalent to the quotient of consecutive
induced cohomology stages. -/
noncomputable def equivQuotient (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) (p : ℤ) :
    Presentation.quotient dPrev dNext F p ≃ₗ[R]
      Stage.quotient dPrev dNext F hcomp p :=
  LinearEquiv.ofBijective (toQuotient dPrev dNext F hcomp hF p)
    (toQuotient_bijective dPrev dNext F hcomp hF p)

end Presentation

/-- Equation `(12.24.5.2)`: the graded piece of the induced cohomology filtration is the
explicit quotient of filtered cycles by next-stage cycles and filtered boundaries. -/
@[stacks 0BDT]
noncomputable def equiv (dPrev : KPrev →ₗ[R] K)
    (dNext : K →ₗ[R] KNext) (F : ℤ → Submodule R K)
    (hcomp : dNext.comp dPrev = 0) (hF : Antitone F) (p : ℤ) :
    (Stage.induced dPrev dNext F hcomp hF).gradedPiece p ≃ₗ[R]
      Presentation.quotient dPrev dNext F p :=
  (equivStage dPrev dNext F hcomp hF p).trans
    (Presentation.equivQuotient dPrev dNext F hcomp hF p).symm

end GradedPiece

end FilteredCohomology
end ModuleCat
