/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower.Monoid
public import ReasLib.CategoryTheory.GradedObject.Total.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# The symmetric algebra as a total commutative monoid object

Unsigned braided totalization sends the ordinarily commutative graded symmetric algebra to a
commutative monoid object of module sheaves.  The construction is direct functor composition,
with a separate theorem exposing its underlying module functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.SymmetricAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- The symmetric algebra functor valued in commutative monoid objects of module sheaves,
obtained by totalizing the canonical graded symmetric algebra. -/
@[stacks 01CF "total symmetric-algebra commutative-monoid functor"]
noncomputable def commMonFunctor :
    ringedSiteModuleCategory J O ⥤ CommMon (ringedSiteModuleCategory J O) :=
  SymmetricPower.commMonFunctor O ⋙
    (GradedObject.Total.functor
      (I := ℕ) (C := ringedSiteModuleCategory J O)).mapCommMon

/-- Forgetting the total symmetric-algebra structure gives the coproduct of the symmetric-power
functor. -/
@[stacks 01CF "underlying module functor of the total symmetric algebra"]
theorem commMonFunctor_comp_forget :
    commMonFunctor O ⋙ CommMon.forget (ringedSiteModuleCategory J O) =
      SymmetricPower.gradedObjectFunctor O ⋙
        GradedObject.Total.functor
          (I := ℕ) (C := ringedSiteModuleCategory J O) := sorry

end SheafOfModules.RingedSite.SymmetricAlgebra
