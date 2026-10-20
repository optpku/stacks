/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

/-!
# Ratio opens for twisting sheaves on projective spectra

The ratio open of a positive degree is the union of the projective basic opens defined by
products of homogeneous elements whose degrees differ by that degree. It is characterized as
the greatest open on which the corresponding multiples of the canonical twisting sheaf are
invertible and their multiplication maps are isomorphisms.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section RatioOpen

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The ratio open of degree `d` is the union of the projective basic opens `D₊(f * g)` for
homogeneous `f` and `g` whose degrees differ by `d`. -/
def projTwistRatioOpen (d : ℕ) : (Proj 𝒜).Opens :=
  ⨆ f : A, ⨆ g : A, ⨆ e : ℕ,
    ⨆ (_ : f ∈ 𝒜 (e + d)), ⨆ (_ : g ∈ 𝒜 e), Proj.basicOpen 𝒜 (f * g)

/-- A projective basic open defined by a product of homogeneous elements whose degrees differ
by `d` is contained in the ratio open of degree `d`. -/
theorem basicOpen_mul_le_projTwistRatioOpen
    {d e : ℕ} {f g : A} (hf : f ∈ 𝒜 (e + d)) (hg : g ∈ 𝒜 e) :
    Proj.basicOpen 𝒜 (f * g) ≤ projTwistRatioOpen 𝒜 d := sorry

end RatioOpen

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]

namespace Proj.AssociatedModule.TwistMultiplication

/-- An open is good for degree `d` and a canonical twist multiplication when every twist whose
index is a multiple of `d` is invertible there and every multiplication between such twists is
an isomorphism there. -/
def IsGoodOpen (T : TwistMultiplication 𝒜) (d : ℕ) (W : (Proj 𝒜).Opens) : Prop :=
  (∀ n : ℤ,
    Scheme.Modules.Invertible
      ((Scheme.Modules.pullback W.ι).obj (twistingSheaf 𝒜 (n * (d : ℤ))))) ∧
  ∀ n m : ℤ,
    IsIso (restrictOpenMap 𝒜 T W (n * (d : ℤ)) (m * (d : ℤ)))

end Proj.AssociatedModule.TwistMultiplication

/-- Every integral multiple of a positive degree gives an invertible canonical twisting sheaf
after restriction to the corresponding ratio open. -/
theorem projTwist_restrict_ratioOpen_invertible
    {d : ℕ} (hd : 0 < d) (n : ℤ) :
    Scheme.Modules.Invertible
      ((Scheme.Modules.pullback (projTwistRatioOpen 𝒜 d).ι).obj
        (Proj.AssociatedModule.twistingSheaf 𝒜 (n * (d : ℤ)))) := sorry

/-- Multiplication of canonical twists whose indices are multiples of a positive degree is an
isomorphism after restriction to the corresponding ratio open. -/
theorem projTwistMul_restrict_ratioOpen_isIso
    (T : Proj.AssociatedModule.TwistMultiplication 𝒜)
    {d : ℕ} (hd : 0 < d) (n m : ℤ) :
    IsIso
      (Proj.AssociatedModule.TwistMultiplication.restrictOpenMap 𝒜 T
        (projTwistRatioOpen 𝒜 d)
        (n * (d : ℤ)) (m * (d : ℤ))) := sorry

/-- Every open that is good for a positive degree and a canonical twist multiplication is
contained in the corresponding ratio open. -/
theorem le_projTwistRatioOpen_of_restrict_invertible_and_mul_isIso
    (T : Proj.AssociatedModule.TwistMultiplication 𝒜)
    {d : ℕ} (hd : 0 < d) (W : (Proj 𝒜).Opens)
    (hW : Proj.AssociatedModule.TwistMultiplication.IsGoodOpen 𝒜 T d W) :
    W ≤ projTwistRatioOpen 𝒜 d := sorry

/-- For a positive degree, the ratio open is the greatest open on which all corresponding
twists are invertible and all corresponding twist multiplication maps are isomorphisms. -/
theorem projTwistRatioOpen_isGreatest
    (T : Proj.AssociatedModule.TwistMultiplication 𝒜)
    {d : ℕ} (hd : 0 < d) :
    IsGreatest
      {W : (Proj 𝒜).Opens |
        Proj.AssociatedModule.TwistMultiplication.IsGoodOpen 𝒜 T d W}
      (projTwistRatioOpen 𝒜 d) := sorry

namespace Proj.AssociatedModule.ShiftComparison

variable {M : Type u} [AddCommGroup M] [Module A M]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]

/-- The comparison between an associated module sheaf tensored with a twist and the associated
sheaf of the shifted grading is an isomorphism on the ratio open at every multiple of its
positive degree. -/
theorem restrictRatioOpen_isIso
    (C : ShiftComparison 𝒜 ℳ) {d : ℕ} (hd : 0 < d) (n : ℤ) :
    IsIso
      (restrictOpenMap 𝒜 ℳ C (projTwistRatioOpen 𝒜 d) (n * (d : ℤ))) := sorry

/-- If a graded ring is generated over its degree-zero part by finitely many homogeneous
elements of positive degrees dividing `d`, then the comparison with every shifted associated
module sheaf is an isomorphism in each degree divisible by `d`. -/
theorem hom_isIso_of_dvd_generatorDegrees
    (C : ShiftComparison 𝒜 ℳ) (d : ℕ) (generators : Finset A)
    (generatorDegree : {x // x ∈ generators} → ℕ)
    (hgenerated : Algebra.adjoin (𝒜 0) (generators : Set A) = ⊤)
    (hhomogeneous : ∀ x : {x // x ∈ generators}, x.1 ∈ 𝒜 (generatorDegree x))
    (hpositive : ∀ x : {x // x ∈ generators}, 0 < generatorDegree x)
    (hd_dvd : ∀ x : {x // x ∈ generators}, generatorDegree x ∣ d)
    (n : ℤ) (hn : (d : ℤ) ∣ n) :
    IsIso (C.hom n) := sorry

end Proj.AssociatedModule.ShiftComparison

end AlgebraicGeometry
