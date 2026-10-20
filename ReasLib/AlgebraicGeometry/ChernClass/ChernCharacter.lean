module

public import Mathlib.RingTheory.PowerSeries.Exp
public import ReasLib.AlgebraicGeometry.ChernClass.Total

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w x

namespace AlgebraicGeometry.ChernClass

namespace ChernCharacter

/-- The formal exponential of an element of a ring over `ℚ`, represented coefficientwise
as a power series. -/
def exp {R : Type u} [Ring R] [Algebra ℚ R] (a : R) : PowerSeries R :=
  PowerSeries.mk fun i ↦ algebraMap ℚ R ((i.factorial : ℚ)⁻¹) * a ^ i

/-- The coefficient of `exp a` in degree `i` is `a ^ i / i!`. -/
theorem coeff_exp {R : Type u} [Ring R] [Algebra ℚ R] (a : R) (i : ℕ) :
    PowerSeries.coeff i (exp a) =
      algebraMap ℚ R ((i.factorial : ℚ)⁻¹) * a ^ i := sorry

end ChernCharacter

/-- A natural Chern character from vector-bundle `K₀` to the completed graded
cohomology ring, normalized on classes of line bundles. -/
structure ChernCharacter
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
    (A : Cᵒᵖ ⥤ RingCat.{x})
    (Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X)))
    [∀ X, GradedAlgebra (Agrade X)]
    (firstChernClass : ∀ X, (toScheme.obj X).PicardGroup →+ Agrade X 1)
    [∀ X, Algebra ℚ (A.obj (Opposite.op X))] where
  /-- The Chern character on the vector-bundle Grothendieck ring. -/
  app : ∀ X, Scheme.VectorBundleK0 (toScheme.obj X) →+*
    PowerSeries (A.obj (Opposite.op X))
  /-- The coefficient of degree `i` belongs to the degree-`i` part of cohomology. -/
  coeff_mem : ∀ X (alpha : Scheme.VectorBundleK0 (toScheme.obj X)) (i : ℕ),
    PowerSeries.coeff i (app X alpha) ∈ Agrade X i
  /-- Chern characters commute with pullback. -/
  naturality : ∀ {X' X : C} (f : X' ⟶ X)
      (alpha : Scheme.VectorBundleK0 (toScheme.obj X)),
    PowerSeries.map (A.map f.op).hom (app X alpha) =
      app X' (Scheme.VectorBundleK0.pullback (toScheme.map f) alpha)
  /-- On a Picard class `L`, the Chern character is `exp(c₁(L))`. -/
  lineBundle : ∀ (X : C) (L : (toScheme.obj X).PicardGroup),
    app X (picardK0Class (toScheme.obj X) L) =
      ChernCharacter.exp (firstChernClass X L : A.obj (Opposite.op X))

namespace ChernCharacter

variable {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
  (A : Cᵒᵖ ⥤ RingCat.{x})
  (Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X)))
  [∀ X, GradedAlgebra (Agrade X)]
  (firstChernClass : ∀ X, (toScheme.obj X).PicardGroup →+ Agrade X 1)
  [∀ X, Algebra ℚ (A.obj (Opposite.op X))]

/-- Two Chern characters are equal when their objectwise ring homomorphisms agree. -/
@[ext]
theorem ext
    (ch ch' : ChernCharacter toScheme A Agrade firstChernClass)
    (h : ∀ X, ch.app X = ch'.app X) : ch = ch' := sorry

/-- On a line-bundle class, the coefficient of degree `i` is
`c₁(L) ^ i / i!`. -/
theorem lineBundle_coeff
    (ch : ChernCharacter toScheme A Agrade firstChernClass)
    (X : C) (L : (toScheme.obj X).PicardGroup) (i : ℕ) :
    PowerSeries.coeff i (ch.app X (picardK0Class (toScheme.obj X) L)) =
      algebraMap ℚ (A.obj (Opposite.op X)) ((i.factorial : ℚ)⁻¹) *
        (firstChernClass X L : A.obj (Opposite.op X)) ^ i := sorry

end ChernCharacter

/-- A graded cohomology theory valued in `ℚ`-algebras admits a unique natural Chern
character on vector-bundle Grothendieck rings with the prescribed line-bundle values. -/
theorem existsUniqueChernCharacter
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
    (A : Cᵒᵖ ⥤ RingCat.{x})
    (Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X)))
    [∀ X, GradedAlgebra (Agrade X)] [∀ X, Algebra ℚ (A.obj (Opposite.op X))]
    (S : CohomologyTheory toScheme A Agrade) :
    ∃ ch : ChernCharacter toScheme A Agrade S.firstChernClass,
      ∀ ch', ch' = ch := sorry

end AlgebraicGeometry.ChernClass
