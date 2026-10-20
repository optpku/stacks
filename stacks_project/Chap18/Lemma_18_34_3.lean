module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.Construction
import StacksCheckRecall

/-!
# Lemma 18.34.3

The reusable differential-operator functor is generic, while the corepresentability theorem and
its canonical additive representation are owned by
`ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.Construction`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}
variable (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)

/- Lemma 18.34.3 (09CT): there exists an `O₂`-module sheaf whose Hom functor is naturally
isomorphic to the functor of order-`k` differential operators out of `F`. -/
@[stacks 09CT]
#check
  (DifferentialOperators.isCorepresentable φ F k :
    (DifferentialOperators.functor φ F k).IsCorepresentable)

end SheafOfModules.RingedSite
