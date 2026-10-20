module

public import ReasLib.AlgebraicGeometry.BivariantClass.OverField
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/- Lemma 42.61.2: for a field `k`, a scheme `X` locally of finite type over `k`, and
`p : ℤ`, degree-`p` bivariant classes for `X ⟶ Spec k` are canonically identified with
`CH_{-p}(X)`. -/
@[stacks 0FBW] #check (AlgebraicGeometry.BivariantClass.chowEquiv :
  {k : Type u} → [Field k] → (X : SchemeOverField k) →
    [LocallyOfFiniteType X.hom] → (p : ℤ) →
      @AddEquiv (BivariantClass (fun _ ↦ 0) (terminal.from X) p)
        (RelativeChow (fun _ ↦ 0) X (-p))
        (@AddSemigroup.toAdd _
          (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (terminal.from X) p).toAddCommMonoid.toAddMonoid.toAddSemigroup)
        inferInstance)
