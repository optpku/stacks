module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Endomorphisms of Distinguished Triangles

This leaf contains the idempotent-lifting calculus for an individual
distinguished triangle.  It is independent of any choice of an
idempotent-completion construction.
-/

namespace CategoryTheory.Pretriangulated.Triangle.Endomorphism

universe v u

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]

/-- Stacks 05QP, Lemma 13.4.5: the composite of the middle components of two endomorphisms of a
distinguished triangle is zero when the first component of the second factor and the third
component of the first factor vanish. -/
@[stacks 05QP]
theorem comp₂_eq_zero {T : CategoryTheory.Pretriangulated.Triangle D}
    (hT : T ∈ distTriang D) (φ φ' : End T)
    (hφ₁ : φ.hom₁ = 0) (hφ'₃ : φ'.hom₃ = 0) :
    φ'.hom₂ ≫ φ.hom₂ = 0 := sorry

/-- Stacks 05QQ, Lemma 13.4.6: compatible idempotent endomorphisms of the outer vertices of a
distinguished triangle extend to an idempotent endomorphism of the triangle. -/
@[stacks 05QQ]
theorem existsIdempotentOfOuter {T : CategoryTheory.Pretriangulated.Triangle D}
    (hT : T ∈ distTriang D) (a : End T.obj₁) (c : End T.obj₃)
    (hcomm : CommSq T.mor₃ c (a⟦(1 : ℤ)⟧') T.mor₃)
    (ha : a ≫ a = a) (hc : c ≫ c = c) :
    ∃ φ : End T, φ.hom₁ = a ∧ φ.hom₃ = c ∧ φ.hom₂ ≫ φ.hom₂ = φ.hom₂ := sorry

end CategoryTheory.Pretriangulated.Triangle.Endomorphism
