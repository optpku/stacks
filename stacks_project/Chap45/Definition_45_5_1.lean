module

public import ReasLib.AlgebraicGeometry.ChowMotive.ChowGroup
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Correspondence

universe u

/- Definition 45.5.1: for a Chow motive `M = (X, p, m)` over `k`, the `i`th Chow
 group is `p (CH^(i + m)(X) ⊗ ℚ)` under the concrete rational Chow realization. -/
@[stacks 0FGL] #check
  (ChowMotive.chowGroup :
    ∀ {k : Type u} [Field k],
      ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) →
        ℤ → ModuleCat.{u + 1} ℚ)

#check (ChowMotive.chowRealization :
  ∀ (k : Type u) [Field k] (i : ℤ),
    Correspondence.GradedCategory k ⥤ ModuleCat.{u + 1} ℚ)

#check (ChowMotive.chowGroup_eq_range :
  ∀ {k : Type u} [Field k],
    ∀ (M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) (i : ℤ),
      ChowMotive.chowGroup M i =
        ModuleCat.of ℚ
          (LinearMap.range ((ChowMotive.chowRealization k i).map M.p).hom))
