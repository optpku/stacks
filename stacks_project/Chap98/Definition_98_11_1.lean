module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreserving
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 98.11.1: a category 𝒳 fibred in groupoids over (Sch/S)_fppf is
limit preserving if for every affine scheme T over S which is a directed inverse
limit T = lim T_i of affine schemes T_i over S, the comparison
colim 𝒳_{T_i} ⟶ 𝒳_T of fibre categories is an equivalence. -/
@[stacks 07XL] #check (AlgebraicGeometry.Groupoids.LimitPreserving :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.GroupoidsOver S → Prop)
