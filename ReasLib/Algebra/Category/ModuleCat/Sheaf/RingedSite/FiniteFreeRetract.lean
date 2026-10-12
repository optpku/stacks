/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Retract
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally finite-free retracts

This file owns the local retract property for a sheaf of modules over an arbitrary sheaf of
rings.  Commutativity and monoidal structure belong to the duality applications, not to the
property itself.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

namespace FiniteFreeRetract

/-- The object property of module sheaves which locally, after every base restriction, belong to
the retract closure of finite free module sheaves. -/
def localProperty (R : Sheaf J RingCat.{w}) :
    ObjectProperty (SheafOfModules.{w} R) :=
  fun M ↦ ∀ U : C,
    ∃ (I : Type (max u v)) (Ui : I → Over U), (J.over U).CoversTop Ui ∧
      ∀ i : I,
        finiteFreeRetractModuleProperty ((R.over U).over (Ui i))
          ((M.over U).over (Ui i))

/-- A module sheaf is locally a retract of a finite free module if its restrictions belong to
`localProperty R`. -/
@[stacks 0FNY "local finite-free retract hypothesis"]
class IsLocal (M : SheafOfModules.{w} R) : Prop where
  /-- Membership in the canonical local finite-free-retract object property. -/
  property : localProperty R M

/-- The typeclass predicate is the proposition represented by `localProperty`. -/
theorem isLocal_iff (M : SheafOfModules.{w} R) :
    IsLocal M ↔ localProperty R M := sorry

/-- The local finite-free-retract property in terms of explicit categorical retracts. -/
theorem isLocal_iff_retract (M : SheafOfModules.{w} R) :
    IsLocal M ↔
      ∀ U : C,
        ∃ (I : Type (max u v)) (Ui : I → Over U), (J.over U).CoversTop Ui ∧
          ∀ i : I,
            ∃ α : Type w, Finite α ∧
              Nonempty
                (Retract ((M.over U).over (Ui i))
                  (SheafOfModules.free α :
                    SheafOfModules.{w} ((R.over U).over (Ui i)))) := sorry

/-- The local finite-free retract property in terms of explicit split maps. -/
theorem isLocal_iff_split (M : SheafOfModules.{w} R) :
    IsLocal M ↔
      ∀ U : C,
        ∃ (I : Type (max u v)) (Ui : I → Over U), (J.over U).CoversTop Ui ∧
          ∀ i : I,
            ∃ α : Type w, Finite α ∧
              ∃ ι :
                  (M.over U).over (Ui i) ⟶
                    (SheafOfModules.free α :
                      SheafOfModules.{w} ((R.over U).over (Ui i))),
                ∃ π :
                    (SheafOfModules.free α :
                      SheafOfModules.{w} ((R.over U).over (Ui i))) ⟶
                      (M.over U).over (Ui i),
                  ι ≫ π = 𝟙 ((M.over U).over (Ui i)) := sorry

/-- Extract a covering family on which a local finite-free retract belongs to the canonical
finite-free retract closure. -/
theorem IsLocal.existsCover {M : SheafOfModules.{w} R} (hM : IsLocal M) (U : C) :
    ∃ (I : Type (max u v)) (Ui : I → Over U), (J.over U).CoversTop Ui ∧
      ∀ i : I,
        finiteFreeRetractModuleProperty ((R.over U).over (Ui i))
          ((M.over U).over (Ui i)) := sorry

/-- The local finite-free-retract object property is stable under categorical retracts. -/
instance localProperty_isStableUnderRetracts :
    (localProperty R).IsStableUnderRetracts := sorry

/-- A retract of a locally finite-free retract is again locally a finite-free retract. -/
theorem IsLocal.ofRetract {M N : SheafOfModules.{w} R}
    (r : Retract M N) (hN : IsLocal N) : IsLocal M := sorry

section FiniteLocallyFree

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A finite locally free module sheaf is locally a finite-free retract. -/
instance isLocal_of_isFiniteLocallyFree
    (M : SheafOfModules.{w} R) [IsFiniteLocallyFree M] : IsLocal M := sorry

end FiniteLocallyFree

end FiniteFreeRetract

end SheafOfModules.RingedSite
