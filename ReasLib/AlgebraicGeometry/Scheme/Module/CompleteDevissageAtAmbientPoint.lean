/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageOver
public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissageAtAmbientPoint

/-!
# Complete dévissages at ambient points

This module refines a complete dévissage over the image of an arbitrary point by chosen
points and compatible ambient-point one-step dévissages.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

namespace OneStepDevissageAtAmbientPoint

variable {S : Scheme.{u}} {X : Over S} {F : X.left.Modules}
  [LocallyOfFiniteType X.hom] [F.IsQuasicoherent] [F.IsFiniteType] {x : X.left}

/-- An ambient-point one-step dévissage has the same scheme-and-module diagram as a specified
stage and immersion of a complete dévissage. -/
structure IsStage {s : S} (D : OneStepDevissageAtAmbientPoint X F x)
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

/-- Construct stage compatibility from exact agreement of the schemes, dependent maps, and
module. -/
theorem ofComponents {s : S} {D : OneStepDevissageAtAmbientPoint X F x}
    {T : CompleteDevissageOver.Stage S s} {i : T.Z ⟶ X}
    (Z_eq : D.toOneStepDevissage.Z = T.Z)
    (Y_eq : D.toOneStepDevissage.Y = T.Y)
    (i_eq : HEq D.toOneStepDevissage.i i)
    (π_eq : HEq D.toOneStepDevissage.π T.π)
    (G_eq : HEq D.toOneStepDevissage.G T.G) : D.IsStage T i where
  Z_eq := Z_eq
  Y_eq := Y_eq
  i_eq := i_eq
  π_eq := π_eq
  G_eq := G_eq

end IsStage

end OneStepDevissageAtAmbientPoint

/-- A complete dévissage at an ambient point `x` consists of a complete dévissage over `f x`,
chosen points in every stage, and compatible ambient-point one-step dévissages at `x` and at
the chosen point of every preceding stage. -/
structure CompleteDevissageAtAmbientPoint {S X : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [h_f : LocallyOfFiniteType f] [h_qc : F.IsQuasicoherent]
    [h_ft : F.IsFiniteType] (x : X) where
  /-- The underlying complete dévissage over the image of `x`. -/
  toCompleteDevissageOver : CompleteDevissageOver f F (f x)
  /-- The chosen point in the auxiliary scheme at every stage. -/
  z (i : Fin (toCompleteDevissageOver.last + 1)) :
    (toCompleteDevissageOver.stage i).Z.left
  /-- The chosen point in the smooth model at every stage. -/
  y (i : Fin (toCompleteDevissageOver.last + 1)) :
    (toCompleteDevissageOver.stage i).Y.left
  /-- The first stage is an ambient-point one-step dévissage at `x`. -/
  initialStep :
    @OneStepDevissageAtAmbientPoint S (Over.mk f) F h_f h_qc h_ft x
  /-- The first one-step dévissage uses exactly the first underlying stage. -/
  initialCompatibility :
    @OneStepDevissageAtAmbientPoint.IsStage S (Over.mk f) F h_f h_qc h_ft x (f x)
      initialStep (toCompleteDevissageOver.stage 0) toCompleteDevissageOver.initial
  /-- Its auxiliary point is the chosen point of the first stage. -/
  initial_z :
    HEq
      (@OneStepDevissageAtAmbientPoint.z S (Over.mk f) F h_f h_qc h_ft x initialStep)
      (z 0)
  /-- Its model point is the chosen point of the first stage. -/
  initial_y :
    HEq
      (@OneStepDevissageAtAmbientPoint.y S (Over.mk f) F h_f h_qc h_ft x initialStep)
      (y 0)
  /-- Each later stage is an ambient-point one-step dévissage of the preceding comparison
  cokernel at the preceding chosen model point. -/
  successorStep (i : Fin toCompleteDevissageOver.last) :
    @OneStepDevissageAtAmbientPoint S (toCompleteDevissageOver.stage i.castSucc).Y
      (cokernel (toCompleteDevissageOver.stage i.castSucc).α)
      (toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
      (toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
      (toCompleteDevissageOver.transitionStep i).sourceFiniteType (y i.castSucc)
  /-- Each later one-step dévissage uses exactly its underlying successor stage. -/
  successorCompatibility (i : Fin toCompleteDevissageOver.last) :
    @OneStepDevissageAtAmbientPoint.IsStage S
      (toCompleteDevissageOver.stage i.castSucc).Y
      (cokernel (toCompleteDevissageOver.stage i.castSucc).α)
      (toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
      (toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
      (toCompleteDevissageOver.transitionStep i).sourceFiniteType (y i.castSucc)
      (f x) (successorStep i) (toCompleteDevissageOver.stage i.succ)
      (toCompleteDevissageOver.transition i)
  /-- Every later auxiliary point is the chosen point of its underlying stage. -/
  successor_z (i : Fin toCompleteDevissageOver.last) :
    HEq
      (@OneStepDevissageAtAmbientPoint.z S
        (toCompleteDevissageOver.stage i.castSucc).Y
        (cokernel (toCompleteDevissageOver.stage i.castSucc).α)
        (toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
        (toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
        (toCompleteDevissageOver.transitionStep i).sourceFiniteType (y i.castSucc)
        (successorStep i))
      (z i.succ)
  /-- Every later model point is the chosen point of its underlying stage. -/
  successor_y (i : Fin toCompleteDevissageOver.last) :
    HEq
      (@OneStepDevissageAtAmbientPoint.y S
        (toCompleteDevissageOver.stage i.castSucc).Y
        (cokernel (toCompleteDevissageOver.stage i.castSucc).α)
        (toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
        (toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
        (toCompleteDevissageOver.transitionStep i).sourceFiniteType (y i.castSucc)
        (successorStep i))
      (y i.succ)

namespace CompleteDevissageAtAmbientPoint

/-- Assemble a complete dévissage at an ambient point from an underlying complete dévissage,
its chosen points, and compatible initial and successor refinements. -/
def ofStages {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    [h_f : LocallyOfFiniteType f] [h_qc : F.IsQuasicoherent]
    [h_ft : F.IsFiniteType] {x : X}
    (D : CompleteDevissageOver f F (f x))
    (z : (i : Fin (D.last + 1)) → (D.stage i).Z.left)
    (y : (i : Fin (D.last + 1)) → (D.stage i).Y.left)
    (initialStep :
      @OneStepDevissageAtAmbientPoint S (Over.mk f) F h_f h_qc h_ft x)
    (initialCompatibility :
      @OneStepDevissageAtAmbientPoint.IsStage S (Over.mk f) F h_f h_qc h_ft x (f x)
        initialStep (D.stage 0) D.initial)
    (initial_z :
      HEq
        (@OneStepDevissageAtAmbientPoint.z S (Over.mk f) F h_f h_qc h_ft x initialStep)
        (z 0))
    (initial_y :
      HEq
        (@OneStepDevissageAtAmbientPoint.y S (Over.mk f) F h_f h_qc h_ft x initialStep)
        (y 0))
    (successorStep : (i : Fin D.last) →
      @OneStepDevissageAtAmbientPoint S (D.stage i.castSucc).Y
        (cokernel (D.stage i.castSucc).α) (D.transitionStep i).locallyOfFiniteType
        (D.transitionStep i).sourceQuasicoherent (D.transitionStep i).sourceFiniteType
        (y i.castSucc))
    (successorCompatibility : ∀ i : Fin D.last,
      @OneStepDevissageAtAmbientPoint.IsStage S (D.stage i.castSucc).Y
        (cokernel (D.stage i.castSucc).α) (D.transitionStep i).locallyOfFiniteType
        (D.transitionStep i).sourceQuasicoherent (D.transitionStep i).sourceFiniteType
        (y i.castSucc) (f x) (successorStep i) (D.stage i.succ) (D.transition i))
    (successor_z : ∀ i : Fin D.last,
      HEq
        (@OneStepDevissageAtAmbientPoint.z S (D.stage i.castSucc).Y
          (cokernel (D.stage i.castSucc).α) (D.transitionStep i).locallyOfFiniteType
          (D.transitionStep i).sourceQuasicoherent (D.transitionStep i).sourceFiniteType
          (y i.castSucc) (successorStep i))
        (z i.succ))
    (successor_y : ∀ i : Fin D.last,
      HEq
        (@OneStepDevissageAtAmbientPoint.y S (D.stage i.castSucc).Y
          (cokernel (D.stage i.castSucc).α) (D.transitionStep i).locallyOfFiniteType
          (D.transitionStep i).sourceQuasicoherent (D.transitionStep i).sourceFiniteType
          (y i.castSucc) (successorStep i))
        (y i.succ)) :
    CompleteDevissageAtAmbientPoint f F x where
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

/-- The initial ambient-point one-step dévissage uses the first underlying stage and its
chosen auxiliary and model points. -/
theorem initialStage {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    [h_f : LocallyOfFiniteType f] [h_qc : F.IsQuasicoherent]
    [h_ft : F.IsFiniteType] {x : X}
    (D : CompleteDevissageAtAmbientPoint f F x) :
    @OneStepDevissageAtAmbientPoint.IsStage S (Over.mk f) F h_f h_qc h_ft x (f x)
        D.initialStep (D.toCompleteDevissageOver.stage 0)
        D.toCompleteDevissageOver.initial ∧
      HEq
          (@OneStepDevissageAtAmbientPoint.z S (Over.mk f) F h_f h_qc h_ft x D.initialStep)
          (D.z 0) ∧
        HEq
            (@OneStepDevissageAtAmbientPoint.y S (Over.mk f) F h_f h_qc h_ft x
              D.initialStep)
            (D.y 0) := sorry

/-- Every successor ambient-point one-step dévissage uses the corresponding underlying stage
and its chosen auxiliary and model points. -/
theorem successorStage {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] {x : X}
    (D : CompleteDevissageAtAmbientPoint f F x)
    (i : Fin D.toCompleteDevissageOver.last) :
    @OneStepDevissageAtAmbientPoint.IsStage S
        (D.toCompleteDevissageOver.stage i.castSucc).Y
        (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
        (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
        (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
        (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType (D.y i.castSucc)
        (f x) (D.successorStep i) (D.toCompleteDevissageOver.stage i.succ)
        (D.toCompleteDevissageOver.transition i) ∧
      HEq
          (@OneStepDevissageAtAmbientPoint.z S
            (D.toCompleteDevissageOver.stage i.castSucc).Y
            (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
            (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
            (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
            (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType (D.y i.castSucc)
            (D.successorStep i))
          (D.z i.succ) ∧
        HEq
          (@OneStepDevissageAtAmbientPoint.y S
            (D.toCompleteDevissageOver.stage i.castSucc).Y
            (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
            (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
            (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
            (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType (D.y i.castSucc)
            (D.successorStep i))
          (D.y i.succ) := sorry

/-- A complete dévissage at an ambient point consists precisely of compatible initial and
successor ambient-point one-step dévissages on its underlying complete dévissage. -/
theorem spec {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    [h_f : LocallyOfFiniteType f] [h_qc : F.IsQuasicoherent]
    [h_ft : F.IsFiniteType] {x : X}
    (D : CompleteDevissageAtAmbientPoint f F x) :
    (@OneStepDevissageAtAmbientPoint.IsStage S (Over.mk f) F h_f h_qc h_ft x (f x)
          D.initialStep (D.toCompleteDevissageOver.stage 0)
          D.toCompleteDevissageOver.initial ∧
        HEq
            (@OneStepDevissageAtAmbientPoint.z S (Over.mk f) F h_f h_qc h_ft x
              D.initialStep)
            (D.z 0) ∧
          HEq
              (@OneStepDevissageAtAmbientPoint.y S (Over.mk f) F h_f h_qc h_ft x
                D.initialStep)
              (D.y 0)) ∧
      ∀ i : Fin D.toCompleteDevissageOver.last,
        @OneStepDevissageAtAmbientPoint.IsStage S
            (D.toCompleteDevissageOver.stage i.castSucc).Y
            (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
            (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
            (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
            (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType (D.y i.castSucc)
            (f x) (D.successorStep i) (D.toCompleteDevissageOver.stage i.succ)
            (D.toCompleteDevissageOver.transition i) ∧
          HEq
              (@OneStepDevissageAtAmbientPoint.z S
                (D.toCompleteDevissageOver.stage i.castSucc).Y
                (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
                (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
                (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
                (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
                (D.y i.castSucc) (D.successorStep i))
              (D.z i.succ) ∧
            HEq
              (@OneStepDevissageAtAmbientPoint.y S
                (D.toCompleteDevissageOver.stage i.castSucc).Y
                (cokernel (D.toCompleteDevissageOver.stage i.castSucc).α)
                (D.toCompleteDevissageOver.transitionStep i).locallyOfFiniteType
                (D.toCompleteDevissageOver.transitionStep i).sourceQuasicoherent
                (D.toCompleteDevissageOver.transitionStep i).sourceFiniteType
                (D.y i.castSucc) (D.successorStep i))
              (D.y i.succ) := sorry

end CompleteDevissageAtAmbientPoint

end AlgebraicGeometry.Scheme.Modules
