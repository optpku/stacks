/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Monoid
public import ReasLib.CategoryTheory.GradedObject.Total.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# The tensor algebra as a total monoid object

The graded tensor-power monoid is sent through the strong monoidal totalization functor.  This
retains the algebra structure on the coproduct of all tensor powers without duplicating either
the graded construction or Mathlib's transport of monoid objects.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.TensorAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (O : Sheaf J CommRingCat.{w})

/-- The tensor algebra functor valued in monoid objects of module sheaves, obtained by
totalizing the canonical graded tensor algebra. -/
@[stacks 01CF "total tensor-algebra monoid functor"]
noncomputable def monFunctor :
    ringedSiteModuleCategory.{u, v, w, w} J O ⥤
      Mon (ringedSiteModuleCategory.{u, v, w, w} J O) :=
  TensorPower.monFunctor O ⋙
    (GradedObject.Total.functor
      (I := ℕ) (C := ringedSiteModuleCategory.{u, v, w, w} J O)).mapMon

/-- Forgetting the total tensor-algebra multiplication gives the coproduct of the tensor-power
functor. -/
@[stacks 01CF "underlying module functor of the total tensor algebra"]
theorem monFunctor_comp_forget :
    monFunctor O ⋙ Mon.forget (ringedSiteModuleCategory.{u, v, w, w} J O) =
      TensorPower.gradedObjectFunctor O ⋙
        GradedObject.Total.functor
          (I := ℕ) (C := ringedSiteModuleCategory.{u, v, w, w} J O) := sorry

end SheafOfModules.RingedSite.TensorAlgebra
