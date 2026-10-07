module

public import ReasLib.Algebra.Group.Action.NatInt.LowerBound
public import ReasLib.Algebra.Module.Graded.Reindex

/-!
# Graded modules on integer degrees bounded below

The canonical graded-module structure on lower-bounded integer pieces is obtained by reindexing
along the equivariant inclusion into `ℤ`.
-/

@[expose] public section

universe u v

namespace DirectSum.Gmodule.LowerBound

/-- The homogeneous module pieces whose integer degrees are bounded below by `k`. -/
abbrev pieces (k : ℤ) (M : ℤ → Type v) : {d : ℤ // k ≤ d} → Type v :=
  fun d ↦ M d.1

section AddMonoid

variable (A : ℕ → Type u) (M : ℤ → Type v)
variable [∀ n, AddMonoid (A n)] [∀ d, AddMonoid (M d)]
variable [GradedMonoid.GMonoid A] [DirectSum.Gmodule A M]

/-- 01CV: the canonical graded module on lower-bounded integer pieces, reindexed along
`AddAction.IntLowerBound.coeHom k`. -/
@[stacks 01CV "graded module on lower-bounded integer pieces"]
instance instGmodule (k : ℤ) : DirectSum.Gmodule A (pieces k M) :=
  DirectSum.Gmodule.reindex (AddAction.IntLowerBound.coeHom k) M

/-- The inferred lower-bounded homogeneous action agrees with the original integer-indexed
homogeneous action. -/
theorem smul_eq (k : ℤ) {n : ℕ} {d : {d : ℤ // k ≤ d}}
    (a : A n) (x : pieces k M d) :
    @GradedMonoid.GSMul.smul ℕ {d : ℤ // k ≤ d} A (pieces k M) _ _ n d a x =
      @GradedMonoid.GSMul.smul ℕ ℤ A M _ _ n d.1 a x := sorry

end AddMonoid

end DirectSum.Gmodule.LowerBound
