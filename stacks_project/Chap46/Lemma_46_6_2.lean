/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Parasitic.SerreQuotient
import StacksCheckRecall

open AlgebraicGeometry

/- Lemma 46.6.2 (1): parasitic adequate modules form a Serre subcategory. -/
@[stacks 06ZN] #check (SheafOfModules.Adeq.Parasitic.isSerreClass :
    ∀ (S : Scheme) (τ : StandardTopology),
      @CategoryTheory.ObjectProperty.IsSerreClass _
        _
        (SheafOfModules.Adeq.instAbelian S τ)
        (SheafOfModules.Adeq.parasitic
          ModuleValuedFunctor.tensorExtensionUnderlying
          (@SheafOfModules.affineEvaluationUnderlying S τ)))

/- Lemma 46.6.2 (2): Zariski restriction induces an equivalence from the
parasitic Serre quotient to `Scheme.QCoh S`. -/
@[stacks 06ZN] #check (SheafOfModules.Adeq.Parasitic.isEquivalence :
    ∀ (S : Scheme) (τ : StandardTopology),
      (SheafOfModules.Adeq.Parasitic.quotientFunctor S τ).IsEquivalence)
