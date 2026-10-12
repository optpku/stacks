/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.Subcomplex.AdjoinSimplex
public import Mathlib.Order.RelSeries

/-!
# Filtrations by adjoining nondegenerate simplices

The structure `singleSimplex.Attachment U W` records the simplex and equations witnessing one
attachment step from `U` to `W`. A `singleSimplex.Filtration V` retains this data at every finite
stage, while `singleSimplex.extensionRel` and `RelSeries` provide a proposition-valued forgetful
view. Finite simplicial sets admit finite filtrations by these steps.
-/

@[expose] public section

open CategoryTheory

universe u

namespace SSet.Subcomplex

variable {V : SSet.{u}}

namespace singleSimplex

/-- The relation on subcomplexes in which the second is obtained from the first by a
single-simplex attachment. -/
@[stacks 018S "single-simplex extension relation"]
def extensionRel (V : SSet.{u}) : SetRel V.Subcomplex V.Subcomplex :=
  { p | Nonempty (Attachment p.1 p.2) }

/-- A single-simplex attachment witnesses the associated extension relation. -/
theorem Attachment.toRel {U W : V.Subcomplex} (A : Attachment U W) :
    (U, W) ∈ extensionRel V := sorry

/-- The extension relation can be constructed directly from a missing nondegenerate simplex,
its boundary condition, and the resulting join equality. -/
theorem extensionRel.ofSimplex {U W : V.Subcomplex} (x : U.N)
    (boundary : x.boundaryRangeLE)
    (adjoin_eq : U ⊔ Subcomplex.ofSimplex x.simplex = W) :
    (U, W) ∈ extensionRel V := sorry

/-- The extension relation has the original existential characterization by a missing
nondegenerate simplex. -/
theorem mem_extensionRel {U W : V.Subcomplex} :
    (U, W) ∈ extensionRel V ↔
      ∃ x : U.N, x.boundaryRangeLE ∧
        U ⊔ Subcomplex.ofSimplex x.simplex = W := sorry

/-- Eliminate an extension-relation witness into a proposition using its attachment data. -/
theorem extensionRel.elim {U W : V.Subcomplex} (h : (U, W) ∈ extensionRel V)
    {P : Prop} (f : Attachment U W → P) : P := sorry

/-- A finite filtration of subcomplexes in which every adjacent pair carries explicit
single-simplex attachment data. -/
@[stacks 018S "attachment-valued single-simplex filtration"]
structure Filtration (V : SSet.{u}) where
  /-- The number of attachment steps. -/
  length : ℕ
  /-- The subcomplex at each stage of the filtration. -/
  stage : Fin (length + 1) → V.Subcomplex
  /-- The explicit single-simplex attachment between each pair of adjacent stages. -/
  attachment : ∀ i : Fin length,
    Attachment (stage (Fin.castSucc i)) (stage i.succ)

namespace Filtration

/-- The filtration with one stage and no attachments. -/
@[stacks 018S "one-stage single-simplex filtration"]
def singleton (U : V.Subcomplex) : Filtration V where
  length := 0
  stage := fun _ => U
  attachment := Fin.elim0

/-- The initial subcomplex of an attachment-valued filtration. -/
@[stacks 018S "initial stage of an attachment-valued filtration"]
def head (F : Filtration V) : V.Subcomplex :=
  F.stage 0

/-- The final subcomplex of an attachment-valued filtration. -/
@[stacks 018S "final stage of an attachment-valued filtration"]
def last (F : Filtration V) : V.Subcomplex :=
  F.stage ⟨F.length, Nat.lt_succ_self F.length⟩

/-- Prepend one attachment to an attachment-valued filtration. -/
@[stacks 018S "prepend an attachment to a filtration"]
def cons (F : Filtration V) {U : V.Subcomplex} (A : Attachment U F.head) :
    Filtration V where
  length := F.length + 1
  stage := Fin.cases U F.stage
  attachment := Fin.cases A F.attachment

/-- The head of a one-stage filtration is its unique stage. -/
@[simp, stacks 018S "head of a one-stage filtration"]
theorem singleton_head (U : V.Subcomplex) :
    (singleton U).head = U := sorry

/-- The last stage of a one-stage filtration is its unique stage. -/
@[simp, stacks 018S "last stage of a one-stage filtration"]
theorem singleton_last (U : V.Subcomplex) :
    (singleton U).last = U := sorry

/-- Prepending an attachment makes its source the head of the filtration. -/
@[simp, stacks 018S "head after prepending an attachment"]
theorem cons_head (F : Filtration V) {U : V.Subcomplex} (A : Attachment U F.head) :
    (F.cons A).head = U := sorry

/-- Prepending an attachment does not change the last stage of the filtration. -/
@[simp, stacks 018S "last stage after prepending an attachment"]
theorem cons_last (F : Filtration V) {U : V.Subcomplex} (A : Attachment U F.head) :
    (F.cons A).last = F.last := sorry

/-- Each filtration stage is contained in the immediately following stage. -/
@[stacks 018S "monotonicity of one filtration step"]
theorem stage_le_succ (F : Filtration V) (i : Fin F.length) :
    F.stage (Fin.castSucc i) ≤ F.stage i.succ := sorry

/-- The stages of an attachment-valued filtration are monotone. -/
@[stacks 018S "monotonicity of filtration stages"]
theorem monotone_stage (F : Filtration V) :
    Monotone F.stage := sorry

/-- Forget the chosen attachment data and retain only the associated relation series. -/
@[stacks 018S "forgetful relation series of an attachment-valued filtration"]
def toRelSeries (F : Filtration V) : RelSeries (extensionRel V) where
  length := F.length
  toFun := F.stage
  step i := (F.attachment i).toRel

/-- Forgetting attachment data preserves the initial subcomplex. -/
@[simp, stacks 018S "filtration forgetful map preserves the head"]
theorem toRelSeries_head (F : Filtration V) :
    F.toRelSeries.head = F.head := sorry

/-- Forgetting attachment data preserves the final subcomplex. -/
@[simp, stacks 018S "filtration forgetful map preserves the last stage"]
theorem toRelSeries_last (F : Filtration V) :
    F.toRelSeries.last = F.last := sorry

/-- The forgetful relation series of a one-stage filtration is the canonical singleton series. -/
@[simp, stacks 018S "forgetful relation series of a one-stage filtration"]
theorem toRelSeries_singleton (U : V.Subcomplex) :
    (singleton U).toRelSeries = RelSeries.singleton (extensionRel V) U := sorry

/-- Forgetting attachment data commutes with prepending an attachment. -/
@[simp, stacks 018S "forgetful relation series after prepending an attachment"]
theorem toRelSeries_cons (F : Filtration V) {U : V.Subcomplex}
    (A : Attachment U F.head) :
    (F.cons A).toRelSeries = F.toRelSeries.cons U A.toRel := sorry

/-- Prove a property of the final stage of an attachment-valued filtration by propagating it
across each explicit attachment. -/
@[stacks 018S "induction over an attachment-valued filtration"]
theorem inductionOn (F : Filtration V) {P : V.Subcomplex → Prop}
    (head : P F.head)
    (step : ∀ {U W : V.Subcomplex}, Attachment U W → P U → P W) :
    P F.last := sorry

end Filtration

/-- Prove a property of the last stage of a single-simplex filtration by proving it at the
head and showing that every explicit attachment preserves it. -/
@[stacks 018S "propagate along a single-simplex relation series"]
theorem RelSeries.inductionLast (s : RelSeries (extensionRel V))
    {P : V.Subcomplex → Prop} (head : P s.head)
    (step : ∀ {U W : V.Subcomplex}, Attachment U W → P U → P W) :
    P s.last := sorry

end singleSimplex

end SSet.Subcomplex
