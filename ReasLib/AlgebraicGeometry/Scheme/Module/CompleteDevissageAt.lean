module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageOver

/-!
# Complete dévissages at support points

This module refines a complete dévissage over the image of a point by chosen
support points and compatible one-step dévissages at those points.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

namespace OneStepDevissageAt

variable {S : Scheme.{u}} {X : Over S} {F : X.left.Modules}
  [LocallyOfFiniteType X.hom] [F.IsQuasicoherent] [F.IsFiniteType] {x : X.left}

/-- A one-step dévissage at a support point has the same scheme-and-module diagram as a
specified stage and immersion of a complete dévissage. -/
structure IsStage {s : S} (D : OneStepDevissageAt X F x)
    (T : CompleteDevissageOver.Stage S s) (i : T.Z ⟶ X) : Prop where
  /-- The auxiliary scheme is the one in the specified stage. -/
  Z_eq : D.toOneStepDevissage.Z = T.Z
  /-- The smooth model is the one in the specified stage. -/
  Y_eq : D.toOneStepDevissage.Y = T.Y
  /-- The closed immersion is the specified stage immersion. -/
  i_eq : HEq D.toOneStepDevissage.i i
  /-- The finite morphism is the one in the specified stage. -/
  π_eq : HEq D.toOneStepDevissage.π T.π
  /-- The auxiliary module is the one in the specified stage. -/
  G_eq : HEq D.toOneStepDevissage.G T.G

namespace IsStage

/-- Exact agreement of the schemes, dependent maps, and module gives compatibility with a
specified stage. -/
theorem ofComponents {s : S} {D : OneStepDevissageAt X F x}
    {T : CompleteDevissageOver.Stage S s} {i : T.Z ⟶ X}
    (Z_eq : D.toOneStepDevissage.Z = T.Z)
    (Y_eq : D.toOneStepDevissage.Y = T.Y)
    (i_eq : HEq D.toOneStepDevissage.i i)
    (π_eq : HEq D.toOneStepDevissage.π T.π)
    (G_eq : HEq D.toOneStepDevissage.G T.G) : D.IsStage T i := sorry

end IsStage

end OneStepDevissageAt

/-- A complete dévissage at a support point `x` consists of a complete dévissage over `f x`,
chosen points in every stage, and compatible one-step dévissages at `x` and at the chosen
point of every preceding stage. -/
structure CompleteDevissageAt {S X : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [h_f : LocallyOfFiniteType f] [h_qc : F.IsQuasicoherent]
    [h_ft : F.IsFiniteType] (x : X) where
  /-- The underlying complete dévissage over the image of `x`. -/
  toCompleteDevissageOver : CompleteDevissageOver f F (f x)
  /-- The chosen point in the auxiliary scheme at every stage. -/
  z (i : Fin (toCompleteDevissageOver.last + 1)) :
    (toCompleteDevissageOver.stage i).Z.left
  /-- The chosen point in the smooth model at every stage. -/
  y (i : Fin (toCompleteDevissageOver.last + 1)) :
    (toCompleteDevissageOver.stage i).Y.left
  /-- The first stage is a one-step dévissage at `x`. -/
  initialStep :
    @OneStepDevissageAt S (Over.mk f) F h_f h_qc h_ft x
  /-- The first one-step dévissage uses exactly the first underlying stage. -/
  initialCompatibility :
    @OneStepDevissageAt.IsStage S (Over.mk f) F h_f h_qc h_ft x (f x) initialStep
      (toCompleteDevissageOver.stage 0) toCompleteDevissageOver.initial
  /-- Its auxiliary point is the chosen point of the first stage. -/
  initial_z :
    HEq
      (@OneStepDevissageAt.z S (Over.mk f) F h_f h_qc h_ft x initialStep)
      (z 0)
  /-- Its model point is the chosen point of the first stage. -/
  initial_y :
    HEq
      (@OneStepDevissageAt.y S (Over.mk f) F h_f h_qc h_ft x initialStep)
      (y 0)
  /-- Each later stage is a one-step dévissage of the preceding comparison cokernel at the
  preceding chosen model point. -/
  successorStep (i : Fin toCompleteDevissageOver.last) :
    @OneStepDevissageAt S (toCompleteDevissageOver.stage i.castSucc).Y
      (cokernel (toCompleteDevissageOver.stage i.castSucc).α)
      (toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
      (toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
      (toCompleteDevissageOver.transitionStep i).sourceFiniteType (y i.castSucc)
  /-- Each later one-step dévissage uses exactly its underlying successor stage. -/
  successorCompatibility (i : Fin toCompleteDevissageOver.last) :
    @OneStepDevissageAt.IsStage S (toCompleteDevissageOver.stage i.castSucc).Y
      (cokernel (toCompleteDevissageOver.stage i.castSucc).α)
      (toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
      (toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
      (toCompleteDevissageOver.transitionStep i).sourceFiniteType (y i.castSucc)
      (f x) (successorStep i) (toCompleteDevissageOver.stage i.succ)
      (toCompleteDevissageOver.transition i)
  /-- Every later auxiliary point is the chosen point of its underlying stage. -/
  successor_z (i : Fin toCompleteDevissageOver.last) :
    HEq
      (@OneStepDevissageAt.z S (toCompleteDevissageOver.stage i.castSucc).Y
        (cokernel (toCompleteDevissageOver.stage i.castSucc).α)
        (toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
        (toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
        (toCompleteDevissageOver.transitionStep i).sourceFiniteType (y i.castSucc)
        (successorStep i))
      (z i.succ)
  /-- Every later model point is the chosen point of its underlying stage. -/
  successor_y (i : Fin toCompleteDevissageOver.last) :
    HEq
      (@OneStepDevissageAt.y S (toCompleteDevissageOver.stage i.castSucc).Y
        (cokernel (toCompleteDevissageOver.stage i.castSucc).α)
        (toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
        (toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
        (toCompleteDevissageOver.transitionStep i).sourceFiniteType (y i.castSucc)
        (successorStep i))
      (y i.succ)

namespace CompleteDevissageAt

/-- Assemble a complete dévissage at a support point from an underlying complete dévissage,
its chosen points, and compatible initial and successor refinements. -/
def ofStages {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    [h_f : LocallyOfFiniteType f] [h_qc : F.IsQuasicoherent]
    [h_ft : F.IsFiniteType] {x : X}
    (D : CompleteDevissageOver f F (f x))
    (z : (i : Fin (D.last + 1)) → (D.stage i).Z.left)
    (y : (i : Fin (D.last + 1)) → (D.stage i).Y.left)
    (initialStep :
      @OneStepDevissageAt S (Over.mk f) F h_f h_qc h_ft x)
    (initialCompatibility :
      @OneStepDevissageAt.IsStage S (Over.mk f) F h_f h_qc h_ft x (f x)
        initialStep (D.stage 0) D.initial)
    (initial_z :
      HEq (@OneStepDevissageAt.z S (Over.mk f) F h_f h_qc h_ft x initialStep) (z 0))
    (initial_y :
      HEq (@OneStepDevissageAt.y S (Over.mk f) F h_f h_qc h_ft x initialStep) (y 0))
    (successorStep : (i : Fin D.last) →
      @OneStepDevissageAt S (D.stage i.castSucc).Y (cokernel (D.stage i.castSucc).α)
        (D.transitionStep i).locallyOfFiniteType
        (D.transitionStep i).sourceQuasicoherent
        (D.transitionStep i).sourceFiniteType (y i.castSucc))
    (successorCompatibility : ∀ i : Fin D.last,
      @OneStepDevissageAt.IsStage S (D.stage i.castSucc).Y
        (cokernel (D.stage i.castSucc).α) (D.transitionStep i).locallyOfFiniteType
        (D.transitionStep i).sourceQuasicoherent (D.transitionStep i).sourceFiniteType
        (y i.castSucc) (f x) (successorStep i) (D.stage i.succ) (D.transition i))
    (successor_z : ∀ i : Fin D.last,
      HEq
        (@OneStepDevissageAt.z S (D.stage i.castSucc).Y
          (cokernel (D.stage i.castSucc).α) (D.transitionStep i).locallyOfFiniteType
          (D.transitionStep i).sourceQuasicoherent (D.transitionStep i).sourceFiniteType
          (y i.castSucc) (successorStep i))
        (z i.succ))
    (successor_y : ∀ i : Fin D.last,
      HEq
        (@OneStepDevissageAt.y S (D.stage i.castSucc).Y
          (cokernel (D.stage i.castSucc).α) (D.transitionStep i).locallyOfFiniteType
          (D.transitionStep i).sourceQuasicoherent (D.transitionStep i).sourceFiniteType
          (y i.castSucc) (successorStep i))
        (y i.succ)) :
    CompleteDevissageAt f F x where
  toCompleteDevissageOver := D
  z := z
  y := y
  initialStep := initialStep
  initialCompatibility := initialCompatibility
  initial_z := initial_z
  initial_y := initial_y
  successorStep := successorStep
  successorCompatibility := successorCompatibility
  successor_z := successor_z
  successor_y := successor_y

/-- The initial one-step dévissage uses the first underlying stage and its chosen auxiliary and
model points. -/
theorem initialStage {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    [h_f : LocallyOfFiniteType f] [h_qc : F.IsQuasicoherent]
    [h_ft : F.IsFiniteType] {x : X}
    (D : CompleteDevissageAt f F x) :
    @OneStepDevissageAt.IsStage S (Over.mk f) F h_f h_qc h_ft x (f x)
        D.initialStep (D.toCompleteDevissageOver.stage 0)
        D.toCompleteDevissageOver.initial ∧
      HEq (@OneStepDevissageAt.z S (Over.mk f) F h_f h_qc h_ft x D.initialStep)
          (D.z 0) ∧
        HEq (@OneStepDevissageAt.y S (Over.mk f) F h_f h_qc h_ft x D.initialStep)
          (D.y 0) := sorry

/-- Every successor one-step dévissage uses the corresponding underlying stage and its chosen
auxiliary and model points. -/
theorem successorStage {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] {x : X}
    (D : CompleteDevissageAt f F x) (i : Fin D.toCompleteDevissageOver.last) :
    @OneStepDevissageAt.IsStage S (D.toCompleteDevissageOver.stage i.castSucc).Y
        (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
        (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
        (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
        (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType (D.y i.castSucc)
        (f x) (D.successorStep i) (D.toCompleteDevissageOver.stage i.succ)
        (D.toCompleteDevissageOver.transition i) ∧
      HEq
          (@OneStepDevissageAt.z S (D.toCompleteDevissageOver.stage i.castSucc).Y
            (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
            (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
            (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
            (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType (D.y i.castSucc)
            (D.successorStep i))
          (D.z i.succ) ∧
        HEq
          (@OneStepDevissageAt.y S (D.toCompleteDevissageOver.stage i.castSucc).Y
            (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
            (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
            (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
            (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType (D.y i.castSucc)
            (D.successorStep i))
          (D.y i.succ) := sorry

/-- A complete dévissage at a support point consists precisely of compatible initial and
successor one-step dévissages on its underlying complete dévissage. -/
theorem spec {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    [h_f : LocallyOfFiniteType f] [h_qc : F.IsQuasicoherent]
    [h_ft : F.IsFiniteType] {x : X}
    (D : CompleteDevissageAt f F x) :
    (@OneStepDevissageAt.IsStage S (Over.mk f) F h_f h_qc h_ft x (f x)
          D.initialStep (D.toCompleteDevissageOver.stage 0)
          D.toCompleteDevissageOver.initial ∧
        HEq (@OneStepDevissageAt.z S (Over.mk f) F h_f h_qc h_ft x D.initialStep)
            (D.z 0) ∧
          HEq (@OneStepDevissageAt.y S (Over.mk f) F h_f h_qc h_ft x D.initialStep)
            (D.y 0)) ∧
      ∀ i : Fin D.toCompleteDevissageOver.last,
        @OneStepDevissageAt.IsStage S (D.toCompleteDevissageOver.stage i.castSucc).Y
            (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
            (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
            (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
            (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType (D.y i.castSucc)
            (f x) (D.successorStep i) (D.toCompleteDevissageOver.stage i.succ)
            (D.toCompleteDevissageOver.transition i) ∧
          HEq
              (@OneStepDevissageAt.z S (D.toCompleteDevissageOver.stage i.castSucc).Y
                (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
                (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
                (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
                (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
                (D.y i.castSucc) (D.successorStep i))
              (D.z i.succ) ∧
            HEq
              (@OneStepDevissageAt.y S (D.toCompleteDevissageOver.stage i.castSucc).Y
                (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
                (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
                (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
                (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
                (D.y i.castSucc) (D.successorStep i))
              (D.y i.succ) := sorry

end CompleteDevissageAt

end AlgebraicGeometry.Scheme.Modules
