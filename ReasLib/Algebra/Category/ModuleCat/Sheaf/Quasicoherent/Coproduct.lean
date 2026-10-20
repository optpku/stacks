module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Constant coproducts of quasicoherent modules

An arbitrary constant coproduct uses one common presentation cover. This is the coproduct
closure needed when a colimit-preserving functor transports free module sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace SheafOfModules.IsQuasicoherent

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A coproduct of a constant family of quasicoherent module sheaves is quasicoherent. -/
@[stacks 01C3 "constant coproduct"]
instance coproductConst (I : Type w) (M : SheafOfModules.{w} R)
    [M.IsQuasicoherent] :
    (∐ fun _ : I ↦ M).IsQuasicoherent := sorry

end SheafOfModules.IsQuasicoherent
