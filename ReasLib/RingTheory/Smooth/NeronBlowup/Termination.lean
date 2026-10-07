module

public import ReasLib.Algebra.Module.Length
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Residue
public import ReasLib.RingTheory.Smooth.NeronBlowup.Iterate
public import ReasLib.RingTheory.Smooth.NeronBlowup.SmoothnessCriterion

/-!
# Termination of affine Neron blowups

The defect used in Neron's argument is the length of the torsion submodule of
the base-changed conormal cokernel.  It is attached to a genuine smooth
surjective presentation, rather than to an abstract transition system.
-/

@[expose] public section

noncomputable section

open Ideal IsLocalRing

universe u v w x

namespace Algebra.DVR.Factorization

variable {R : Type u} {L : Type v}
variable [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [CommRing L] [IsDomain L] [IsDiscreteValuationRing L]
variable [Algebra R L]

/-- A finite-presentation surjection `B → A` whose presenting algebra is smooth at the
closed center induced from the target DVR. -/
@[stacks 0BJ6]
structure CenteredSmoothPresentation (S : Algebra.DVR.Factorization R L) where
  /-- The underlying surjective presentation of `A → L`. -/
  presentation : S.toTarget.SurjectivePresentation.{u, w, v, x}
  /-- The presenting algebra is finitely presented over the source DVR. -/
  finitePresentation : Algebra.FinitePresentation R presentation.B
  /-- The presenting algebra is smooth at the prime induced by the closed point of `L`. -/
  smoothAtCenter :
    Algebra.SmoothAtPrime R presentation.B presentation.closedCenterPoint

attribute [instance] CenteredSmoothPresentation.finitePresentation

namespace CenteredSmoothPresentation

/-- Build a centered smooth presentation from a surjective presentation whose presenting algebra
is finitely presented and smooth at the induced closed center. -/
@[stacks 0BJ6 "centered smooth presentation constructor"]
def of
    {S : Algebra.DVR.Factorization R L}
    (presentation : S.toTarget.SurjectivePresentation)
    [Algebra.FinitePresentation R presentation.B]
    (smoothAtCenter :
      Algebra.SmoothAtPrime R presentation.B presentation.closedCenterPoint) :
    S.CenteredSmoothPresentation where
  presentation := presentation
  finitePresentation := inferInstance
  smoothAtCenter := smoothAtCenter

variable {S : Algebra.DVR.Factorization R L} (P : S.CenteredSmoothPresentation)

/-- The base-changed conormal cokernel of a centered smooth presentation. -/
@[stacks 0BJ6 "centered conormal cokernel"]
abbrev ConormalCokernel :=
  P.presentation.ConormalCokernel

/-- The torsion submodule of the base-changed conormal cokernel. -/
@[stacks 0BJ6 "centered conormal torsion"]
abbrev torsion : Submodule L P.ConormalCokernel :=
  Submodule.torsion L P.ConormalCokernel

/-- The torsion in the conormal cokernel of a centered smooth presentation is Artinian. -/
@[stacks 0BJ6 "centered conormal torsion is Artinian"]
instance instIsArtinianTorsion : IsArtinian L P.torsion := sorry

/-- The Neron defect: the length of the torsion in the base-changed conormal cokernel. -/
@[stacks 0BJ6]
noncomputable def defect : ℕ :=
  Module.torsionNatLength L P.ConormalCokernel

/-- The Neron defect recovers the `ℕ∞`-valued module length after coercion. -/
@[stacks 0BJ6 "Neron defect equals torsion length", simp, norm_cast]
theorem coe_defect :
    (P.defect : ℕ∞) = Module.length L P.torsion := sorry

/-- The Neron defect vanishes exactly when its torsion submodule is trivial. -/
@[stacks 0BJ6 "zero Neron defect", simp]
theorem defect_eq_zero_iff_torsion_eq_bot :
    P.defect = 0 ↔ P.torsion = (⊥ : Submodule L P.ConormalCokernel) := sorry

/-- The Neron defect vanishes exactly when the conormal cokernel is torsion-free. -/
@[stacks 0BJ6 "zero Neron defect iff torsion-free", simp]
theorem defect_eq_zero_iff_isTorsionFree :
    P.defect = 0 ↔ Module.IsTorsionFree L P.ConormalCokernel := sorry

variable [IsExtensionOfDiscreteValuationRings R L]
variable [IsExtensionOfDiscreteValuationRings.WeaklyUnramified R L]

/-- Under generic smoothness, vanishing of the Neron defect is equivalent to smoothness at the
closed center. -/
@[stacks 0BJ6]
theorem defect_eq_zero_iff_smoothAtClosedCenter
    (hgeneric : Algebra.SmoothAtPrime R S.mid S.genericPoint) :
    P.defect = 0 ↔ Algebra.SmoothAtPrime R S.mid S.closedPoint := sorry

/-- Every DVR factorization admits a centered smooth presentation, for
example one coming from a polynomial presentation. -/
@[stacks 0BJ6 "centered smooth presentation existence"]
theorem nonempty (S : Algebra.DVR.Factorization R L) :
    Nonempty S.CenteredSmoothPresentation := sorry

end CenteredSmoothPresentation

variable [IsExtensionOfDiscreteValuationRings R L]
variable [IsExtensionOfDiscreteValuationRings.WeaklyUnramified R L]

/-- If the current center is not smooth, one affine Neron blowup admits a centered smooth
presentation with strictly smaller torsion defect. -/
@[stacks 0BJ6]
theorem NeronBlowup.exists_defect_lt
    (S : Algebra.DVR.Factorization R L) (P : S.CenteredSmoothPresentation)
    (π : R) (hπ : Irreducible π)
    [Algebra.IsSeparable (ResidueField R) (ResidueField L)]
    (hgeneric : Algebra.SmoothAtPrime R S.mid S.genericPoint)
    (hnot : ¬ Algebra.SmoothAtPrime R S.mid S.closedPoint) :
    ∃ P' : (S.neronBlowupStage π hπ).CenteredSmoothPresentation,
      P'.defect < P.defect := sorry

/-- Lemma 16.4.5 (tag 0BJ6): after finitely many deterministic affine Neron blowups, a
factorization that is smooth at its generic center becomes smooth at its closed center. -/
@[stacks 0BJ6]
theorem NeronBlowup.exists_smooth_iterate
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π)
    [Algebra.IsSeparable (ResidueField R) (ResidueField L)]
    (hgeneric : Algebra.SmoothAtPrime R S.mid S.genericPoint) :
    ∃ n : ℕ,
      Algebra.SmoothAtPrime R (S.iteratedNeronBlowup π hπ n).mid
        (S.iteratedNeronBlowup π hπ n).closedPoint := sorry

end Algebra.DVR.Factorization
