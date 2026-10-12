/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.GradedPiece
public import ReasLib.CategoryTheory.Filtration.Category

/-!
# Morphisms Which Shift a Filtration

This file defines filtered morphisms of filtration degree `r`: an ambient morphism has this
property when it carries stage `p` into stage `p+r`.  Such a morphism has canonical maps on the
shifted stages and on the corresponding graded pieces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FilteredObject.Hom

variable {X Y Z : FilteredObject C}

/-- A filtered morphism raises the filtration by `r` when it maps stage `p` into stage `p+r` for
every integer `p`. -/
@[stacks 012N "morphism raising a filtration"]
def RaisesFiltrationBy (f : X ⟶ Y) (r : ℤ) : Prop :=
  ∀ p : ℤ,
    (Y.filtration.stage (p + r)).Factors
      ((X.filtration.stage p).arrow ≫ f.hom)

/-- Every filtered morphism raises the filtration by zero. -/
theorem raisesFiltrationBy_zero (f : X ⟶ Y) : f.RaisesFiltrationBy 0 := sorry

/-- Filtration shifts add under composition. -/
theorem RaisesFiltrationBy.comp {f : X ⟶ Y} {g : Y ⟶ Z} {r s : ℤ}
    (hf : f.RaisesFiltrationBy r) (hg : g.RaisesFiltrationBy s) :
    (f ≫ g).RaisesFiltrationBy (r + s) := sorry

namespace RaisesFiltrationBy

variable {f : X ⟶ Y} {r : ℤ}

/-- The map from stage `p` of the source to stage `p+r` of the target. -/
@[stacks 012N "shifted filtration-stage map"]
noncomputable def stageMap (hf : f.RaisesFiltrationBy r) (p : ℤ) :
    X.stage p ⟶ Y.stage (p + r) :=
  (Y.filtration.stage (p + r)).factorThru
    ((X.filtration.stage p).arrow ≫ f.hom) (hf p)

/-- The shifted stage map recovers the ambient morphism after inclusion. -/
@[simp]
theorem stageMap_arrow (hf : f.RaisesFiltrationBy r) (p : ℤ) :
    hf.stageMap p ≫ (Y.filtration.stage (p + r)).arrow =
      (X.filtration.stage p).arrow ≫ f.hom := sorry

/-- The shifted stage map is independent of the proof that the morphism raises the filtration. -/
@[stacks 012N "proof irrelevance for shifted stage maps"]
theorem stageMap_proof_irrel (hf hf' : f.RaisesFiltrationBy r) (p : ℤ) :
    hf.stageMap p = hf'.stageMap p := sorry

/-- Shifted stage maps are compatible with consecutive source stages after inclusion into the
ambient target object. -/
theorem stageMap_succ_arrow (hf : f.RaisesFiltrationBy r) (p : ℤ) :
    X.filtration.succInclusion p ≫
        hf.stageMap p ≫ (Y.filtration.stage (p + r)).arrow =
      hf.stageMap (p + 1) ≫ (Y.filtration.stage (p + 1 + r)).arrow := sorry

section GradedPiece

variable [HasZeroMorphisms C] [HasCokernels C]

/-- The shifted stage map followed by the target quotient annihilates the next source stage. -/
theorem gradedPieceMap_condition (hf : f.RaisesFiltrationBy r) (p : ℤ) :
    X.filtration.succInclusion p ≫
        (hf.stageMap p ≫ cokernel.π (Y.filtration.succInclusion (p + r))) =
      0 := sorry

/-- The map `X.gradedPiece p ⟶ Y.gradedPiece (p+r)` induced by a morphism which raises the
filtration by `r`. -/
@[stacks 012N "shifted map on graded pieces"]
noncomputable def gradedPieceMap (hf : f.RaisesFiltrationBy r) (p : ℤ) :
    X.gradedPiece p ⟶ Y.gradedPiece (p + r) :=
  cokernel.desc
    (X.filtration.succInclusion p)
    (hf.stageMap p ≫ cokernel.π (Y.filtration.succInclusion (p + r)))
    (gradedPieceMap_condition hf p)

/-- The shifted map on graded pieces is independent of the proof that the morphism raises the
filtration. -/
@[stacks 012N "proof irrelevance for shifted graded-piece maps"]
theorem gradedPieceMap_proof_irrel (hf hf' : f.RaisesFiltrationBy r) (p : ℤ) :
    hf.gradedPieceMap p = hf'.gradedPieceMap p := sorry

/-- The shifted graded-piece map is characterized by its composite with the source quotient. -/
@[reassoc (attr := simp)]
theorem π_gradedPieceMap (hf : f.RaisesFiltrationBy r) (p : ℤ) :
    cokernel.π (X.filtration.succInclusion p) ≫ hf.gradedPieceMap p =
      hf.stageMap p ≫ cokernel.π (Y.filtration.succInclusion (p + r)) := sorry

end GradedPiece

end RaisesFiltrationBy

end FilteredObject.Hom

end CategoryTheory
