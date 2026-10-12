/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree

/-!
# Resolution properties for sheaves of modules

The resolution property requires finite-type quasi-coherent sheaves of modules to admit
epimorphisms from finite locally free sheaves.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {R : Sheaf J RingCat.{w}}

/-- A sheaf of modules has the resolution property when every finite-type quasi-coherent
module admits an epimorphism from a finite locally free module. -/
def HasResolutionProperty (R : Sheaf J RingCat.{w}) : Prop :=
  ∀ (F : SheafOfModules.{w} R) [F.IsQuasicoherent] [F.IsFiniteType],
    ∃ (E : SheafOfModules.{w} R) (_ : E.IsFiniteLocallyFree) (q : E ⟶ F), Epi q

/-- The resolution property is characterized by finite locally free epimorphic presentations
of finite-type quasi-coherent sheaves of modules. -/
theorem hasResolutionProperty_iff (R : Sheaf J RingCat.{w}) :
    HasResolutionProperty R ↔
      ∀ (F : SheafOfModules.{w} R) [F.IsQuasicoherent] [F.IsFiniteType],
        ∃ (E : SheafOfModules.{w} R) (_ : E.IsFiniteLocallyFree) (q : E ⟶ F), Epi q := sorry

/-- A sheaf with the resolution property supplies a finite locally free epimorphic presentation
of every finite-type quasi-coherent sheaf of modules. -/
theorem HasResolutionProperty.existsQuotient {R : Sheaf J RingCat.{w}}
    (hR : HasResolutionProperty R) (F : SheafOfModules.{w} R)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ (E : SheafOfModules.{w} R) (_ : E.IsFiniteLocallyFree) (q : E ⟶ F), Epi q := sorry

end SheafOfModules
