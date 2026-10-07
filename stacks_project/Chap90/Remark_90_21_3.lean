module

public import stacks_project.Chap90.Remark_90_21_3_Groupoid

/-!
# Identity and inverse morphisms of a groupoid in functors
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]

/-- Remark 90.21.3 (1): a groupoid in functors on `C` has a unique morphism of
functors `e : U ⟶ R` sending each object `x ∈ U.obj T` to the identity arrow on
`x` in the fibre groupoid `(U.obj T, R.obj T, s, t, c)`. -/
@[stacks 06K5]
theorem isIdentity_iff (G : GroupoidInFunctors C) (e' : G.U ⟶ G.R) :
    IsIdentity G e' ↔ e' = G.e := sorry

/-- Remark 90.21.3 (2): a groupoid in functors on `C` has a unique morphism of
functors `i : R ⟶ R` sending each arrow `a ∈ R.obj T` to the inverse of `a` in
the fibre groupoid `(U.obj T, R.obj T, s, t, c)`. -/
@[stacks 06K5]
theorem isInverse_iff (G : GroupoidInFunctors C) (i' : G.R ⟶ G.R) :
    IsInverse G i' ↔ i' = G.i := sorry

end CategoryTheory.GroupoidInFunctors
