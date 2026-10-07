module

public import Mathlib.SetTheory.ZFC.VonNeumann
public import Mathlib.ModelTheory.Substructures

@[expose] public section

universe u v w

noncomputable section

namespace FirstOrder

namespace Language

/-- The type of relations for the language of set theory, consisting of a single binary membership
relation. -/
inductive setTheoryRel : ℕ → Type
  | mem : setTheoryRel 2
  deriving DecidableEq

/-- The language of set theory, consisting of a single binary membership relation. -/
protected def setTheory : Language := ⟨fun _ => Empty, setTheoryRel⟩
  deriving IsRelational

/-- The membership relation symbol in the language of set theory. -/
abbrev mem : Language.setTheory.Relations 2 := .mem

end Language

end FirstOrder

namespace ZFSet

open FirstOrder FirstOrder.Language.Structure

/-- The language of set theory is interpreted on `ZFSet` by native membership. -/
instance instSetTheoryStructure : Language.setTheory.Structure ZFSet.{u} where
  RelMap | .mem => fun x ↦ x 0 ∈ x 1

/-- The membership symbol is realized as `ZFSet` membership. -/
theorem relMap_mem {x y : ZFSet.{u}} : RelMap Language.mem ![x, y] ↔ x ∈ y := sorry

/-- The `Language.setTheory`-substructure with carrier `M`. Relativization of a formula to `M` is
satisfaction in this substructure. -/
def toSubstructure (M : ZFSet.{u}) : Language.setTheory.Substructure ZFSet.{u} where
  carrier := M
  fun_mem {_} f := isEmptyElim f

/-- Membership in `M.toSubstructure` agrees with membership in `M`. -/
theorem mem_toSubstructure {M x : ZFSet.{u}} : x ∈ M.toSubstructure ↔ x ∈ M := sorry

/-- A formula `φ` is reflected by `M` when, for every tuple from `M`, satisfaction of `φ` in
`ZFSet` agrees with satisfaction in `M.toSubstructure`. -/
def Reflects {α : Type v} (M : ZFSet.{u}) (φ : Language.setTheory.Formula α) : Prop :=
  ∀ v : α → M.toSubstructure, φ.Realize (M.toSubstructure.subtype ∘ v) ↔ φ.Realize v

/-- If `M` reflects `φ`, then realization of `φ` on tuples from `M` is absolute between `ZFSet` and
`M.toSubstructure`. -/
theorem reflects_realize {α : Type v} {M : ZFSet.{u}} {φ : Language.setTheory.Formula α}
    (h : Reflects M φ) (v : α → M.toSubstructure) :
    φ.Realize (M.toSubstructure.subtype ∘ v) ↔ φ.Realize v := sorry

/-- A finite conjunction of formulas is reflected by `M` if each conjunct is. -/
theorem reflects_iInf {α : Type v} {ι : Type w} [Finite ι] {M : ZFSet.{u}}
    {φ : ι → Language.setTheory.Formula α} (h : ∀ i, Reflects M (φ i)) :
    Reflects M (Language.Formula.iInf φ) := sorry

end ZFSet
