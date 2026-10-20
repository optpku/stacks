module

public import ReasLib.RingTheory.GradedAlgebra.Nat
public import ReasLib.Algebra.Module.Graded.Compatibility
import StacksCheckRecall

@[expose] public section

/- Definition 111.26.3 (1): a naturally graded algebra is constructed from its
homogeneous multiplication and direct-sum decomposition data. -/
@[stacks 027Z]
#check (GradedAlgebra.ofNatDecomposition :
  ∀ {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [DirectSum.Decomposition 𝒜]
    (hmul : ∀ {n m : ℕ} {x y : B}, x ∈ 𝒜 n → y ∈ 𝒜 m → x * y ∈ 𝒜 (n + m)),
    GradedAlgebra 𝒜)

/- Definition 111.26.3 (2): an integer-graded module over a naturally graded
algebra is characterized by scalar-tower compatibility and homogeneous degree shift. -/
@[stacks 027Z]
#check (GradedModule.IsCompatible :
  ∀ {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] (𝒜 : ℕ → Submodule A B)
    [GradedAlgebra 𝒜] (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ], Prop)
