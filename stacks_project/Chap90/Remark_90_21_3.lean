module

public import ReasLib.CategoryTheory.Groupoid.InFunctors.IdentityInverse
import StacksCheckRecall

/-!
# Identity and inverse morphisms of a groupoid in functors
-/

@[expose] public section

open CategoryTheory

universe u v w

/- Remark 90.21.3 (1): a groupoid in functors on `C` has a unique morphism of
functors `e : U ⟶ R` sending each object `x ∈ U.obj T` to the identity arrow on
`x` in the fibre groupoid `(U.obj T, R.obj T, s, t, c)`. -/
@[stacks 06K5]
#check (CategoryTheory.GroupoidInFunctors.isIdentity_iff :
  ∀ {C : Type u} [Category.{v} C] (G : GroupoidInFunctors.{u, v, w} C)
    (e' : G.U ⟶ G.R), CategoryTheory.GroupoidInFunctors.IsIdentity G e' ↔ e' = G.e)

/- Remark 90.21.3 (2): a groupoid in functors on `C` has a unique morphism of
functors `i : R ⟶ R` sending each arrow `a ∈ R.obj T` to the inverse of `a` in
the fibre groupoid `(U.obj T, R.obj T, s, t, c)`. -/
@[stacks 06K5]
#check (CategoryTheory.GroupoidInFunctors.isInverse_iff :
  ∀ {C : Type u} [Category.{v} C] (G : GroupoidInFunctors.{u, v, w} C)
    (i' : G.R ⟶ G.R), CategoryTheory.GroupoidInFunctors.IsInverse G i' ↔ i' = G.i)
