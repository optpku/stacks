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

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical comparison from a restricted pushforward to the pushforward of a
restriction. It is adjoint to pushing forward the restriction unit on the auxiliary
scheme, using the commutative square of the two open immersions. -/
def restrictPushforwardMap {Z Y : Scheme.{u}} (π : Z ⟶ Y) (G : Z.Modules)
    (U : Z.Opens) (V : Y.Opens) (e : U ≤ π ⁻¹ᵁ V) :
    ((pushforward π).obj G).restrict V.ι ⟶
      (pushforward (π.resLE V U e)).obj (G.restrict U.ι) :=
  ((restrictAdjunction V.ι).homEquiv _ _).symm
    ((pushforward π).map ((restrictAdjunction U.ι).unit.app G) ≫
      (pushforwardComp U.ι π).hom.app (G.restrict U.ι) ≫
      (pushforwardCongr (Scheme.Hom.resLE_comp_ι π e).symm).hom.app
        (G.restrict U.ι) ≫
      (pushforwardComp (π.resLE V U e) V.ι).inv.app (G.restrict U.ι))

/-- Restrict a comparison from a finite free sheaf using the canonical free-sheaf
restriction isomorphism and the canonical restriction/pushforward comparison. No
invertibility of the pushforward comparison is needed to define this map. -/
def restrictFreeComparison {Z Y : Scheme.{u}} (π : Z ⟶ Y) (G : Z.Modules) (rank : ℕ)
    (α : (SheafOfModules.freeFin rank : Y.Modules) ⟶ (pushforward π).obj G)
    (U : Z.Opens) (V : Y.Opens) (e : U ≤ π ⁻¹ᵁ V) :
    (SheafOfModules.freeFin rank : V.toScheme.Modules) ⟶
      (pushforward (π.resLE V U e)).obj (G.restrict U.ι) :=
  SheafOfModules.mapFree (restrictFunctor V.ι) (ULift.{u} (Fin rank))
      (restrictUnitIso V.ι).inv ≫
    (restrictFunctor V.ι).map α ≫ restrictPushforwardMap π G U V e

/-- On each standard basis summand, the restricted comparison is the restriction of
the original summand map followed by the canonical pushforward comparison. -/
theorem ιFree_restrictFreeComparison {Z Y : Scheme.{u}} (π : Z ⟶ Y) (G : Z.Modules)
    (rank : ℕ)
    (α : (SheafOfModules.freeFin rank : Y.Modules) ⟶ (pushforward π).obj G)
    (U : Z.Opens) (V : Y.Opens) (e : U ≤ π ⁻¹ᵁ V) (j : ULift.{u} (Fin rank)) :
    SheafOfModules.ιFree j ≫ restrictFreeComparison π G rank α U V e =
      (restrictUnitIso V.ι).inv ≫
        (restrictFunctor V.ι).map (SheafOfModules.ιFree j ≫ α) ≫
          restrictPushforwardMap π G U V e := by
  simp [restrictFreeComparison, Functor.map_comp, Category.assoc]
  rfl

namespace CompleteDevissageOver.Stage

/-- The rank and comparison map of a stage are the restrictions of those of the
original stage. This property is independent of the distinguished-point conditions. -/
structure IsComparisonRestriction {S : Scheme.{u}} {s : S}
    (T : Stage S s) (B : S.Opens) (U : T.Z.left.Opens) (V : T.Y.left.Opens)
    (hUV : U ≤ T.π.left ⁻¹ᵁ V)
    {s' : B.toScheme} (T' : Stage B.toScheme s') : Prop where
  /-- Restriction retains the rank of the comparison source. -/
  rank_eq : T'.rank = T.rank
  /-- The restricted comparison is the canonical restriction of the original map. -/
  α_eq : HEq T'.α
    (restrictFreeComparison T.π.left T.G T.rank T.α U V hUV)

end CompleteDevissageOver.Stage

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint

variable {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
  [h_f : LocallyOfFiniteType f] [h_qc : F.IsQuasicoherent]
  [h_ft : F.IsFiniteType] {x : X}

/-- A standard shrinking of a complete dévissage at an ambient point consists of
compatible standard shrinkings of its one-step stages over one common base open,
together with the resulting complete dévissage of the restricted source module.
Every stage retains its rank and uses the canonical restriction of its comparison map. -/
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
  /-- Every chosen auxiliary open maps into the corresponding chosen model open. -/
  auxiliary_le_model (i : Fin (D.toCompleteDevissageOver.last + 1)) :
    auxiliary i ≤ (D.toCompleteDevissageOver.stage i).π.left ⁻¹ᵁ model i
  /-- The comparison map at every restricted stage is the canonical restriction of the
  comparison map at the corresponding original stage, with the same rank. -/
  restricted_comparison (i : Fin (D.toCompleteDevissageOver.last + 1)) :
    let h_lft' :=
      @OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedLocallyOfFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial
    let h_qc' :=
      @OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedQuasicoherent S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial
    let h_ft' :=
      @OneStepDevissageAtAmbientPoint.StandardShrinking.restrictedFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial
    let D' := @CompleteDevissageAtAmbientPoint.toCompleteDevissageOver _ _ _ _
      h_lft' h_qc' h_ft' _ restricted
    CompleteDevissageOver.Stage.IsComparisonRestriction
      (D.toCompleteDevissageOver.stage i)
      (@OneStepDevissageAtAmbientPoint.StandardShrinking.base S (Over.mk f) F
        h_f h_qc h_ft x D.initialStep initial)
      (auxiliary i) (model i)
      (auxiliary_le_model i)
      (D'.stage (Fin.cast (by
        simpa [D'] using congrArg Nat.succ restricted_last.symm) i))

namespace StandardShrinking

/-- The stagewise restriction specification carried by a complete shrinking. -/
def comparisonRestriction {D : CompleteDevissageAtAmbientPoint f F x}
    (W : D.StandardShrinking) (i : Fin (D.toCompleteDevissageOver.last + 1)) : Prop :=
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
  CompleteDevissageOver.Stage.IsComparisonRestriction
    (D.toCompleteDevissageOver.stage i)
    (@OneStepDevissageAtAmbientPoint.StandardShrinking.base S (Over.mk f) F
      h_f h_qc h_ft x D.initialStep W₀)
    (W.auxiliary i) (W.model i)
    (W.auxiliary_le_model i) (D'.stage (Fin.cast (by
      simpa [D'] using congrArg Nat.succ W.restricted_last.symm) i))

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

/-- The restricted complete dévissage has the same length and the stored one-step
restrictions. Every stage, including the terminal stage, retains its rank and the
canonical restriction of its comparison map. -/
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
    (∀ i, HEq (@CompleteDevissageAtAmbientPoint.successorStep _ _ _ _
        h_lft' h_qc' h_ft' _ W' (Fin.cast W.restricted_last.symm i))
      (@OneStepDevissageAtAmbientPoint.StandardShrinking.restricted S
        (D.toCompleteDevissageOver.stage i.castSucc).Y
        (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
        (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
        (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
        (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
        (D.y i.castSucc) (D.successorStep i) (W.successor i))) ∧
    ∀ i, (W.auxiliary i ≤ (D.toCompleteDevissageOver.stage i).π.left ⁻¹ᵁ W.model i) ∧
      comparisonRestriction W i := by
  exact ⟨⟨W.restricted_last, W.restricted_initial⟩, W.restricted_successor,
    fun i ↦ ⟨W.auxiliary_le_model i, W.restricted_comparison i⟩⟩

end StandardShrinking

end AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint

namespace AlgebraicGeometry.Scheme.Modules.CompleteDevissageAt

variable {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
  [h_f : LocallyOfFiniteType f] [h_qc : F.IsQuasicoherent]
  [h_ft : F.IsFiniteType] {x : X}

/-- A standard shrinking of a complete dévissage at a support point consists of
compatible standard shrinkings of its one-step stages over one common base open,
together with the resulting complete dévissage of the restricted source module.
Every stage retains its rank and uses the canonical restriction of its comparison map. -/
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
  /-- Every chosen auxiliary open maps into the corresponding chosen model open. -/
  auxiliary_le_model (i : Fin (D.toCompleteDevissageOver.last + 1)) :
    auxiliary i ≤ (D.toCompleteDevissageOver.stage i).π.left ⁻¹ᵁ model i
  /-- The comparison map at every restricted stage is the canonical restriction of the
  comparison map at the corresponding original stage, with the same rank. -/
  restricted_comparison (i : Fin (D.toCompleteDevissageOver.last + 1)) :
    let h_lft' :=
      @OneStepDevissageAt.StandardShrinking.restrictedLocallyOfFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial
    let h_qc' :=
      @OneStepDevissageAt.StandardShrinking.restrictedQuasicoherent S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial
    let h_ft' :=
      @OneStepDevissageAt.StandardShrinking.restrictedFiniteType S
        (Over.mk f) F h_f h_qc h_ft x D.initialStep initial
    let D' := @CompleteDevissageAt.toCompleteDevissageOver _ _ _ _
      h_lft' h_qc' h_ft' _ restricted
    CompleteDevissageOver.Stage.IsComparisonRestriction
      (D.toCompleteDevissageOver.stage i)
      (@OneStepDevissageAt.StandardShrinking.base S (Over.mk f) F
        h_f h_qc h_ft x D.initialStep initial)
      (auxiliary i) (model i)
      (auxiliary_le_model i)
      (D'.stage (Fin.cast (by
        simpa [D'] using congrArg Nat.succ restricted_last.symm) i))

namespace StandardShrinking

/-- The stagewise restriction specification carried by a support-point shrinking. -/
def comparisonRestriction {D : CompleteDevissageAt f F x}
    (W : D.StandardShrinking) (i : Fin (D.toCompleteDevissageOver.last + 1)) : Prop :=
  let W₀ := @CompleteDevissageAt.StandardShrinking.initial S X f F
    h_f h_qc h_ft x D W
  let W' := @CompleteDevissageAt.StandardShrinking.restricted S X f F
    h_f h_qc h_ft x D W
  let h_lft' :=
    @OneStepDevissageAt.StandardShrinking.restrictedLocallyOfFiniteType S
      (Over.mk f) F h_f h_qc h_ft x D.initialStep W₀
  let h_qc' :=
    @OneStepDevissageAt.StandardShrinking.restrictedQuasicoherent S
      (Over.mk f) F h_f h_qc h_ft x D.initialStep W₀
  let h_ft' :=
    @OneStepDevissageAt.StandardShrinking.restrictedFiniteType S
      (Over.mk f) F h_f h_qc h_ft x D.initialStep W₀
  let D' := @CompleteDevissageAt.toCompleteDevissageOver _ _ _ _
    h_lft' h_qc' h_ft' _ W'
  CompleteDevissageOver.Stage.IsComparisonRestriction
    (D.toCompleteDevissageOver.stage i)
    (@OneStepDevissageAt.StandardShrinking.base S (Over.mk f) F
      h_f h_qc h_ft x D.initialStep W₀)
    (W.auxiliary i) (W.model i)
    (W.auxiliary_le_model i) (D'.stage (Fin.cast (by
      simpa [D'] using congrArg Nat.succ W.restricted_last.symm) i))

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

/-- The restricted complete dévissage has the same length and the stored one-step
restrictions. Every stage, including the terminal stage, retains its rank and the
canonical restriction of its comparison map. -/
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
    (∀ i, HEq (@CompleteDevissageAt.successorStep _ _ _ _ h_lft' h_qc' h_ft' _ W'
        (Fin.cast W.restricted_last.symm i))
      (@OneStepDevissageAt.StandardShrinking.restricted S
        (D.toCompleteDevissageOver.stage i.castSucc).Y
        (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
        (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
        (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
        (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
        (D.y i.castSucc) (D.successorStep i) (W.successor i))) ∧
    ∀ i, (W.auxiliary i ≤ (D.toCompleteDevissageOver.stage i).π.left ⁻¹ᵁ W.model i) ∧
      comparisonRestriction W i := by
  exact ⟨⟨W.restricted_last, W.restricted_initial⟩, W.restricted_successor,
    fun i ↦ ⟨W.auxiliary_le_model i, W.restricted_comparison i⟩⟩

end StandardShrinking

end AlgebraicGeometry.Scheme.Modules.CompleteDevissageAt
