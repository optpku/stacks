/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageAtAmbientPoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageAt
public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissage.StandardShrinking

/-!
# Standard shrinkings of complete dévissages

This module assembles compatible standard shrinkings of all one-step stages of a
complete dévissage, both at ambient points and at points in the relevant fibre supports.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint

variable {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
  [h_f : LocallyOfFiniteType f] [h_qc : F.IsQuasicoherent]
  [h_ft : F.IsFiniteType] {x : X}

/-- A standard shrinking of a complete dévissage at an ambient point consists of
compatible standard shrinkings of its one-step stages over one common base open,
together with the resulting complete dévissage of the restricted source module. -/
structure StandardShrinking (D : CompleteDevissageAtAmbientPoint f F x) where
  /-- The standard shrinking of the initial one-step dévissage. -/
  initial :
    @OneStepDevissageAtAmbientPoint.StandardShrinking S (Over.mk f) F
      h_f h_qc h_ft x D.initialStep
  /-- The standard shrinkings of the successor one-step dévissages. -/
  successor (i : Fin D.toCompleteDevissageOver.last) :
    @OneStepDevissageAtAmbientPoint.StandardShrinking S
      (D.toCompleteDevissageOver.stage i.castSucc).Y
      (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
      (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
      (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
      (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
      (D.y i.castSucc) (D.successorStep i)
  /-- The chosen auxiliary open in every stage of the original dévissage. -/
  auxiliary (i : Fin (D.toCompleteDevissageOver.last + 1)) :
    (D.toCompleteDevissageOver.stage i).Z.left.Opens
  /-- The chosen model open in every stage of the original dévissage. -/
  model (i : Fin (D.toCompleteDevissageOver.last + 1)) :
    (D.toCompleteDevissageOver.stage i).Y.left.Opens
  /-- The initial auxiliary open is the stage-zero auxiliary open. -/
  initial_auxiliary :
    HEq (@OneStepDevissageAtAmbientPoint.StandardShrinking.auxiliary S
      (Over.mk f) F h_f h_qc h_ft x D.initialStep initial) (auxiliary 0)
  /-- The initial model open is the stage-zero model open. -/
  initial_model :
    HEq (@OneStepDevissageAtAmbientPoint.StandardShrinking.model S
      (Over.mk f) F h_f h_qc h_ft x D.initialStep initial) (model 0)
  /-- Every successor auxiliary open is its corresponding stage open. -/
  successor_auxiliary (i : Fin D.toCompleteDevissageOver.last) :
    HEq (@OneStepDevissageAtAmbientPoint.StandardShrinking.auxiliary S
      (D.toCompleteDevissageOver.stage i.castSucc).Y
      (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
      (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
      (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
      (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
      (D.y i.castSucc) (D.successorStep i) (successor i)) (auxiliary i.succ)
  /-- Every successor model open is its corresponding stage open. -/
  successor_model (i : Fin D.toCompleteDevissageOver.last) :
    HEq (@OneStepDevissageAtAmbientPoint.StandardShrinking.model S
      (D.toCompleteDevissageOver.stage i.castSucc).Y
      (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
      (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
      (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
      (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
      (D.y i.castSucc) (D.successorStep i) (successor i)) (model i.succ)
  /-- All one-step shrinkings use the same base open. -/
  successor_base (i : Fin D.toCompleteDevissageOver.last) :
    @OneStepDevissageAtAmbientPoint.StandardShrinking.base S
      (D.toCompleteDevissageOver.stage i.castSucc).Y
      (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
      (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
      (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
      (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
      (D.y i.castSucc) (D.successorStep i) (successor i) =
        @OneStepDevissageAtAmbientPoint.StandardShrinking.base S
          (Over.mk f) F h_f h_qc h_ft x D.initialStep initial
  /-- The source open of a successor is the preceding chosen model open. -/
  successor_source (i : Fin D.toCompleteDevissageOver.last) :
    @OneStepDevissageAtAmbientPoint.StandardShrinking.source S
      (D.toCompleteDevissageOver.stage i.castSucc).Y
      (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
      (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
      (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
      (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
      (D.y i.castSucc) (D.successorStep i) (successor i) = model i.castSucc
  /-- The complete dévissage on the restricted source module. -/
  restricted :
    let base := @OneStepDevissageAtAmbientPoint.StandardShrinking.base S
      (Over.mk f) F h_f h_qc h_ft x D.initialStep initial
    let source := @OneStepDevissageAtAmbientPoint.StandardShrinking.source S
      (Over.mk f) F h_f h_qc h_ft x D.initialStep initial
    @CompleteDevissageAtAmbientPoint base.toScheme source.toScheme
      (f.resLE base source
        (@OneStepDevissageAtAmbientPoint.StandardShrinking.source_le_base S
          (Over.mk f) F h_f h_qc h_ft x D.initialStep initial))
      (@Scheme.Modules.restrict source.toScheme X F source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      (@OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedLocallyOfFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      (@OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedQuasicoherent S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      (@OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      ⟨x, @OneStepDevissageAtAmbientPoint.StandardShrinking.sourcePoint_mem S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial⟩
  /-- Restriction preserves the number of stages. -/
  restricted_last :
    @CompleteDevissageOver.last _ _ _ _
      (@OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedLocallyOfFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      (@OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedQuasicoherent S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      (@OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      _ (@CompleteDevissageAtAmbientPoint.toCompleteDevissageOver _ _ _ _
        (@OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedLocallyOfFiniteType S
          (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
        (@OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedQuasicoherent S
          (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
        (@OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedFiniteType S
          (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
        _ restricted) = D.toCompleteDevissageOver.last
  /-- The initial restricted step is the stored initial one-step restriction. -/
  restricted_initial :
    HEq (@CompleteDevissageAtAmbientPoint.initialStep _ _ _ _
      (@OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedLocallyOfFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      (@OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedQuasicoherent S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      (@OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      _ restricted)
      (@OneStepDevissageAtAmbientPoint.StandardShrinking.restricted S (Over.mk f) F
        h_f h_qc h_ft x D.initialStep initial)
  /-- Every successor restricted step is the stored one-step restriction. -/
  restricted_successor (i : Fin D.toCompleteDevissageOver.last) :
    HEq (@CompleteDevissageAtAmbientPoint.successorStep _ _ _ _
      (@OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedLocallyOfFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      (@OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedQuasicoherent S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      (@OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      _ restricted (Fin.cast restricted_last.symm i))
      (@OneStepDevissageAtAmbientPoint.StandardShrinking.restricted S
        (D.toCompleteDevissageOver.stage i.castSucc).Y
        (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
        (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
        (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
        (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
        (D.y i.castSucc) (D.successorStep i) (successor i))

namespace StandardShrinking

/-- Construct a complete standard shrinking from its explicit stagewise shrinkings,
compatible indexed opens, and restricted complete dévissage. -/
def ofRestrictions (D : CompleteDevissageAtAmbientPoint f F x) :=
  @CompleteDevissageAtAmbientPoint.StandardShrinking.mk S X f F h_f h_qc h_ft x D

/-- The common base open of a complete standard shrinking. -/
def base {D : CompleteDevissageAtAmbientPoint f F x} (W : D.StandardShrinking) : S.Opens :=
  @OneStepDevissageAtAmbientPoint.StandardShrinking.base S (Over.mk f) F
    h_f h_qc h_ft x D.initialStep
      (@CompleteDevissageAtAmbientPoint.StandardShrinking.initial S X f F
        h_f h_qc h_ft x D W)

/-- The common source open of a complete standard shrinking. -/
def source {D : CompleteDevissageAtAmbientPoint f F x} (W : D.StandardShrinking) : X.Opens :=
  @OneStepDevissageAtAmbientPoint.StandardShrinking.source S (Over.mk f) F
    h_f h_qc h_ft x D.initialStep
      (@CompleteDevissageAtAmbientPoint.StandardShrinking.initial S X f F
        h_f h_qc h_ft x D W)

/-- The common base and source opens, and all indexed auxiliary and model opens, are
basic opens of global sections. -/
theorem standardOpen_spec {D : CompleteDevissageAtAmbientPoint f F x}
    (W : D.StandardShrinking) :
    ((∃ a : Γ(S, ⊤), W.base = S.basicOpen a) ∧
      ∃ a : Γ(X, ⊤), W.source = X.basicOpen a) ∧
    ((∀ i, ∃ a : Γ((D.toCompleteDevissageOver.stage i).Z.left, ⊤),
        W.auxiliary i = (D.toCompleteDevissageOver.stage i).Z.left.basicOpen a) ∧
      ∀ i, ∃ a : Γ((D.toCompleteDevissageOver.stage i).Y.left, ⊤),
        W.model i = (D.toCompleteDevissageOver.stage i).Y.left.basicOpen a) := sorry

/-- The image of the distinguished point, the point itself, and all chosen stage points
belong to their corresponding standard opens. -/
theorem point_mem_spec {D : CompleteDevissageAtAmbientPoint f F x}
    (W : D.StandardShrinking) :
    (f x ∈ W.base ∧ x ∈ W.source) ∧
      ((∀ i, D.z i ∈ W.auxiliary i) ∧ ∀ i, D.y i ∈ W.model i) := sorry

/-- The restricted complete dévissage has the same length and consists exactly of the
stored restricted initial and successor one-step dévissages. -/
theorem restriction_spec {D : CompleteDevissageAtAmbientPoint f F x}
    (W : D.StandardShrinking) :
    let W₀ := @CompleteDevissageAtAmbientPoint.StandardShrinking.initial S X f F
      h_f h_qc h_ft x D W
    let W' := @CompleteDevissageAtAmbientPoint.StandardShrinking.restricted S X f F
      h_f h_qc h_ft x D W
    let h_lft' :=
      @OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedLocallyOfFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep W₀
    let h_qc' :=
      @OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedQuasicoherent S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep W₀
    let h_ft' :=
      @OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep W₀
    let D' := @CompleteDevissageAtAmbientPoint.toCompleteDevissageOver _ _ _ _
      h_lft' h_qc' h_ft' _ W'
    (@CompleteDevissageOver.last _ _ _ _ h_lft' h_qc' h_ft' _ D' =
        D.toCompleteDevissageOver.last ∧
      HEq (@CompleteDevissageAtAmbientPoint.initialStep _ _ _ _
          h_lft' h_qc' h_ft' _ W')
        (@OneStepDevissageAtAmbientPoint.StandardShrinking.restricted S (Over.mk f) F
          h_f h_qc h_ft x D.initialStep W₀)) ∧
    ∀ i, HEq (@CompleteDevissageAtAmbientPoint.successorStep _ _ _ _
        h_lft' h_qc' h_ft' _ W' (Fin.cast W.restricted_last.symm i))
      (@OneStepDevissageAtAmbientPoint.StandardShrinking.restricted S
        (D.toCompleteDevissageOver.stage i.castSucc).Y
        (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
        (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
        (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
        (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
        (D.y i.castSucc) (D.successorStep i) (W.successor i)) := sorry

end StandardShrinking

end AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint

namespace AlgebraicGeometry.Scheme.Modules.CompleteDevissageAt

variable {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
  [h_f : LocallyOfFiniteType f] [h_qc : F.IsQuasicoherent]
  [h_ft : F.IsFiniteType] {x : X}

/-- A standard shrinking of a complete dévissage at a support point consists of
compatible standard shrinkings of its one-step stages over one common base open,
together with the resulting complete dévissage of the restricted source module. -/
structure StandardShrinking (D : CompleteDevissageAt f F x) where
  /-- The standard shrinking of the initial one-step dévissage. -/
  initial :
    @OneStepDevissageAt.StandardShrinking S (Over.mk f) F h_f h_qc h_ft x
      D.initialStep
  /-- The standard shrinkings of the successor one-step dévissages. -/
  successor (i : Fin D.toCompleteDevissageOver.last) :
    @OneStepDevissageAt.StandardShrinking S
      (D.toCompleteDevissageOver.stage i.castSucc).Y
      (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
      (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
      (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
      (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
      (D.y i.castSucc) (D.successorStep i)
  /-- The chosen auxiliary open in every stage of the original dévissage. -/
  auxiliary (i : Fin (D.toCompleteDevissageOver.last + 1)) :
    (D.toCompleteDevissageOver.stage i).Z.left.Opens
  /-- The chosen model open in every stage of the original dévissage. -/
  model (i : Fin (D.toCompleteDevissageOver.last + 1)) :
    (D.toCompleteDevissageOver.stage i).Y.left.Opens
  /-- The initial auxiliary open is the stage-zero auxiliary open. -/
  initial_auxiliary :
    HEq (@OneStepDevissageAt.StandardShrinking.auxiliary S (Over.mk f) F h_f h_qc h_ft x
      D.initialStep initial) (auxiliary 0)
  /-- The initial model open is the stage-zero model open. -/
  initial_model :
    HEq (@OneStepDevissageAt.StandardShrinking.model S (Over.mk f) F h_f h_qc h_ft x
      D.initialStep initial) (model 0)
  /-- Every successor auxiliary open is its corresponding stage open. -/
  successor_auxiliary (i : Fin D.toCompleteDevissageOver.last) :
    HEq (@OneStepDevissageAt.StandardShrinking.auxiliary S
      (D.toCompleteDevissageOver.stage i.castSucc).Y
      (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
      (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
      (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
      (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
      (D.y i.castSucc) (D.successorStep i) (successor i)) (auxiliary i.succ)
  /-- Every successor model open is its corresponding stage open. -/
  successor_model (i : Fin D.toCompleteDevissageOver.last) :
    HEq (@OneStepDevissageAt.StandardShrinking.model S
      (D.toCompleteDevissageOver.stage i.castSucc).Y
      (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
      (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
      (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
      (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
      (D.y i.castSucc) (D.successorStep i) (successor i)) (model i.succ)
  /-- All one-step shrinkings use the same base open. -/
  successor_base (i : Fin D.toCompleteDevissageOver.last) :
    @OneStepDevissageAt.StandardShrinking.base S
      (D.toCompleteDevissageOver.stage i.castSucc).Y
      (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
      (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
      (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
      (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
      (D.y i.castSucc) (D.successorStep i) (successor i) =
        @OneStepDevissageAt.StandardShrinking.base S (Over.mk f) F h_f h_qc h_ft x
          D.initialStep initial
  /-- The source open of a successor is the preceding chosen model open. -/
  successor_source (i : Fin D.toCompleteDevissageOver.last) :
    @OneStepDevissageAt.StandardShrinking.source S
      (D.toCompleteDevissageOver.stage i.castSucc).Y
      (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
      (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
      (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
      (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
      (D.y i.castSucc) (D.successorStep i) (successor i) = model i.castSucc
  /-- The complete dévissage on the restricted source module. -/
  restricted :
    let base := @OneStepDevissageAt.StandardShrinking.base S (Over.mk f) F
      h_f h_qc h_ft x D.initialStep initial
    let source := @OneStepDevissageAt.StandardShrinking.source S (Over.mk f) F
      h_f h_qc h_ft x D.initialStep initial
    @CompleteDevissageAt base.toScheme source.toScheme
      (f.resLE base source
        (@OneStepDevissageAt.StandardShrinking.source_le_base S (Over.mk f) F
          h_f h_qc h_ft x D.initialStep initial))
      (@Scheme.Modules.restrict source.toScheme X F source.ι
        (Scheme.Opens.instIsOpenImmersionι source))
      (@OneStepDevissageAt.StandardShrinking.restrictedLocallyOfFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      (@OneStepDevissageAt.StandardShrinking.restrictedQuasicoherent S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      (@OneStepDevissageAt.StandardShrinking.restrictedFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      ⟨x, @OneStepDevissageAt.StandardShrinking.sourcePoint_mem S (Over.mk f) F
        h_f h_qc h_ft x D.initialStep initial⟩
  /-- Restriction preserves the number of stages. -/
  restricted_last :
    @CompleteDevissageOver.last _ _ _ _
      (@OneStepDevissageAt.StandardShrinking.restrictedLocallyOfFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      (@OneStepDevissageAt.StandardShrinking.restrictedQuasicoherent S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      (@OneStepDevissageAt.StandardShrinking.restrictedFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      _ (@CompleteDevissageAt.toCompleteDevissageOver _ _ _ _
        (@OneStepDevissageAt.StandardShrinking.restrictedLocallyOfFiniteType S
          (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
        (@OneStepDevissageAt.StandardShrinking.restrictedQuasicoherent S
          (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
        (@OneStepDevissageAt.StandardShrinking.restrictedFiniteType S
          (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
        _ restricted) = D.toCompleteDevissageOver.last
  /-- The initial restricted step is the stored initial one-step restriction. -/
  restricted_initial :
    HEq (@CompleteDevissageAt.initialStep _ _ _ _
      (@OneStepDevissageAt.StandardShrinking.restrictedLocallyOfFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      (@OneStepDevissageAt.StandardShrinking.restrictedQuasicoherent S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      (@OneStepDevissageAt.StandardShrinking.restrictedFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      _ restricted)
      (@OneStepDevissageAt.StandardShrinking.restricted S (Over.mk f) F
        h_f h_qc h_ft x D.initialStep initial)
  /-- Every successor restricted step is the stored one-step restriction. -/
  restricted_successor (i : Fin D.toCompleteDevissageOver.last) :
    HEq (@CompleteDevissageAt.successorStep _ _ _ _
      (@OneStepDevissageAt.StandardShrinking.restrictedLocallyOfFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      (@OneStepDevissageAt.StandardShrinking.restrictedQuasicoherent S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      (@OneStepDevissageAt.StandardShrinking.restrictedFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial)
      _ restricted (Fin.cast restricted_last.symm i))
      (@OneStepDevissageAt.StandardShrinking.restricted S
        (D.toCompleteDevissageOver.stage i.castSucc).Y
        (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
        (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
        (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
        (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
        (D.y i.castSucc) (D.successorStep i) (successor i))

namespace StandardShrinking

/-- Construct a complete standard shrinking from its explicit stagewise shrinkings,
compatible indexed opens, and restricted complete dévissage. -/
def ofRestrictions (D : CompleteDevissageAt f F x) :=
  @CompleteDevissageAt.StandardShrinking.mk S X f F h_f h_qc h_ft x D

/-- The common base and source opens, and all indexed auxiliary and model opens, are
basic opens of global sections. -/
theorem standardOpen_spec {D : CompleteDevissageAt f F x} (W : D.StandardShrinking) :
    let W₀ := @CompleteDevissageAt.StandardShrinking.initial S X f F
      h_f h_qc h_ft x D W
    ((∃ a : Γ(S, ⊤),
        @OneStepDevissageAt.StandardShrinking.base S (Over.mk f) F
          h_f h_qc h_ft x D.initialStep W₀ = S.basicOpen a) ∧
      ∃ a : Γ(X, ⊤),
        @OneStepDevissageAt.StandardShrinking.source S (Over.mk f) F
          h_f h_qc h_ft x D.initialStep W₀ = X.basicOpen a) ∧
    ((∀ i, ∃ a : Γ((D.toCompleteDevissageOver.stage i).Z.left, ⊤),
        W.auxiliary i = (D.toCompleteDevissageOver.stage i).Z.left.basicOpen a) ∧
      ∀ i, ∃ a : Γ((D.toCompleteDevissageOver.stage i).Y.left, ⊤),
        W.model i = (D.toCompleteDevissageOver.stage i).Y.left.basicOpen a) := sorry

/-- The image of the distinguished point, the point itself, and all chosen stage points
belong to their corresponding standard opens. -/
theorem point_mem_spec {D : CompleteDevissageAt f F x} (W : D.StandardShrinking) :
    let W₀ := @CompleteDevissageAt.StandardShrinking.initial S X f F
      h_f h_qc h_ft x D W
    (f x ∈ @OneStepDevissageAt.StandardShrinking.base S (Over.mk f) F
        h_f h_qc h_ft x D.initialStep W₀ ∧
      x ∈ @OneStepDevissageAt.StandardShrinking.source S (Over.mk f) F
        h_f h_qc h_ft x D.initialStep W₀) ∧
      ((∀ i, D.z i ∈ W.auxiliary i) ∧ ∀ i, D.y i ∈ W.model i) := sorry

/-- The restricted complete dévissage has the same length and consists exactly of the
stored restricted initial and successor one-step dévissages. -/
theorem restriction_spec {D : CompleteDevissageAt f F x} (W : D.StandardShrinking) :
    let W₀ := @CompleteDevissageAt.StandardShrinking.initial S X f F
      h_f h_qc h_ft x D W
    let W' := @CompleteDevissageAt.StandardShrinking.restricted S X f F
      h_f h_qc h_ft x D W
    let h_lft' := @OneStepDevissageAt.StandardShrinking.restrictedLocallyOfFiniteType S
      (Over.mk f) F h_f h_qc h_ft x D.initialStep W₀
    let h_qc' := @OneStepDevissageAt.StandardShrinking.restrictedQuasicoherent S
      (Over.mk f) F h_f h_qc h_ft x D.initialStep W₀
    let h_ft' := @OneStepDevissageAt.StandardShrinking.restrictedFiniteType S
      (Over.mk f) F h_f h_qc h_ft x D.initialStep W₀
    let D' := @CompleteDevissageAt.toCompleteDevissageOver _ _ _ _
      h_lft' h_qc' h_ft' _ W'
    (@CompleteDevissageOver.last _ _ _ _ h_lft' h_qc' h_ft' _ D' =
        D.toCompleteDevissageOver.last ∧
      HEq (@CompleteDevissageAt.initialStep _ _ _ _ h_lft' h_qc' h_ft' _ W')
        (@OneStepDevissageAt.StandardShrinking.restricted S (Over.mk f) F
          h_f h_qc h_ft x D.initialStep W₀)) ∧
    ∀ i, HEq (@CompleteDevissageAt.successorStep _ _ _ _ h_lft' h_qc' h_ft' _ W'
        (Fin.cast W.restricted_last.symm i))
      (@OneStepDevissageAt.StandardShrinking.restricted S
        (D.toCompleteDevissageOver.stage i.castSucc).Y
        (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
        (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
        (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
        (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
        (D.y i.castSucc) (D.successorStep i) (W.successor i)) := sorry

end StandardShrinking

end AlgebraicGeometry.Scheme.Modules.CompleteDevissageAt
