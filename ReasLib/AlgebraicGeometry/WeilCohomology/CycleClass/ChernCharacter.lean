/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.CycleClass
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Pullback
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

open Algebra.TensorProduct AlgebraicGeometry CategoryTheory
open scoped BigOperators TensorProduct

noncomputable section

universe u v w x y z q

namespace WeilCohomology

/-- The scalar extension of vector-bundle `K₀` from `ℤ` to `ℚ`. -/
abbrev RationalK0 {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w}) (X : C) :=
  TensorProduct ℤ ℚ (Scheme.VectorBundleK0 (toScheme.obj X))

namespace RationalK0

/-- The canonical map from integral vector-bundle `K₀` to its rationalization. -/
noncomputable def rationalization
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w}) (X : C) :
    Scheme.VectorBundleK0 (toScheme.obj X) →+* RationalK0 toScheme X :=
  includeRight.toRingHom

/-- Pullback on rationalized vector-bundle `K₀`. -/
noncomputable def pullback
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
    {X Y : C} (f : X ⟶ Y) : RationalK0 toScheme Y →+* RationalK0 toScheme X :=
  (Algebra.TensorProduct.map (AlgHom.id ℚ ℚ)
    (Scheme.VectorBundleK0.pullback (toScheme.map f)).toIntAlgHom).toRingHom

/-- The canonical rational extension of a ring homomorphism from integral vector-bundle `K₀`
to a `ℚ`-algebra. -/
noncomputable def extend
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w}) {X : C}
    {R : Type x} [Ring R] [Algebra ℚ R]
    (f : Scheme.VectorBundleK0 (toScheme.obj X) →+* R) : RationalK0 toScheme X →+* R :=
  ((AlgHom.liftEquiv ℤ ℚ (Scheme.VectorBundleK0 (toScheme.obj X)) R) f.toIntAlgHom).toRingHom

/-- Restricting a canonical rational extension to integral `K₀` recovers the original map. -/
theorem extend_rationalization
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w}) {X : C}
    {R : Type x} [Ring R] [Algebra ℚ R]
    (f : Scheme.VectorBundleK0 (toScheme.obj X) →+* R) :
    (extend toScheme f).comp (rationalization toScheme X) = f := sorry

/-- Ring homomorphisms from rationalized `K₀` into a `ℚ`-algebra are determined by their
restriction to integral `K₀`. -/
theorem hom_ext
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w}) {X : C}
    {R : Type x} [Ring R] [Algebra ℚ R]
    (f g : RationalK0 toScheme X →+* R)
    (h : f.comp (rationalization toScheme X) = g.comp (rationalization toScheme X)) :
    f = g := sorry

end RationalK0

/-- The scalar extension of an integral Chow ring from `ℤ` to `ℚ`. -/
abbrev RationalChow {C : Type u} (CH₀ : C → Type x) [∀ X, CommRing (CH₀ X)] (X : C) :=
  TensorProduct ℤ ℚ (CH₀ X)

namespace RationalChow

/-- The canonical map from an integral Chow ring to its rationalization. -/
noncomputable def rationalization
    {C : Type u} (CH₀ : C → Type x) [∀ X, CommRing (CH₀ X)] (X : C) :
    CH₀ X →+* RationalChow CH₀ X :=
  includeRight.toRingHom

/-- The canonical rational extension of a ring homomorphism from an integral Chow ring
to a `ℚ`-algebra. -/
noncomputable def extend
    {C : Type u} (CH₀ : C → Type x) [∀ X, CommRing (CH₀ X)] {X : C}
    {R : Type y} [Ring R] [Algebra ℚ R]
    (f : CH₀ X →+* R) : RationalChow CH₀ X →+* R :=
  ((AlgHom.liftEquiv ℤ ℚ (CH₀ X) R) f.toIntAlgHom).toRingHom

/-- Restricting the rational extension of an integral Chow homomorphism recovers the
original homomorphism. -/
theorem extend_rationalization
    {C : Type u} (CH₀ : C → Type x) [∀ X, CommRing (CH₀ X)] {X : C}
    {R : Type y} [Ring R] [Algebra ℚ R]
    (f : CH₀ X →+* R) :
    (extend CH₀ f).comp (rationalization CH₀ X) = f := sorry

/-- Homomorphisms from rationalized Chow rings are determined by their restrictions to
the integral Chow ring. -/
theorem hom_ext
    {C : Type u} (CH₀ : C → Type x) [∀ X, CommRing (CH₀ X)] {X : C}
    {R : Type y} [Ring R] [Algebra ℚ R]
    (f g : RationalChow CH₀ X →+* R)
    (h : f.comp (rationalization CH₀ X) = g.comp (rationalization CH₀ X)) :
    f = g := sorry

/-- The rationalized pullback induced by an integral graded Chow pullback. -/
noncomputable def pullback
    {C : Type u} [Category.{v} C] (CH₀ : C → Type x) [∀ X, CommRing (CH₀ X)]
    (CHgrade : ∀ X, ℤ → Submodule ℤ (CH₀ X)) [∀ X, GradedAlgebra (CHgrade X)]
    (cyclePullback : ∀ {X Y : C}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X)
    {X Y : C} (f : X ⟶ Y) : RationalChow CH₀ Y →+* RationalChow CH₀ X :=
  (Algebra.TensorProduct.map (AlgHom.id ℚ ℚ)
    (cyclePullback f).toAlgHom.toIntAlgHom).toRingHom

/-- The rationalized codimension-`i` part of an integral graded Chow ring. -/
noncomputable def grade
    {C : Type u} (CH₀ : C → Type x) [∀ X, CommRing (CH₀ X)]
    (CHgrade : ∀ X, ℤ → Submodule ℤ (CH₀ X)) (X : C) (i : ℕ) :
    Submodule ℤ (RationalChow CH₀ X) :=
  LinearMap.range (TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
    (CHgrade X (i : ℤ)).subtype)

end RationalChow

/-- A pullback-natural comparison identifying rationalized vector-bundle `K₀` with
rational Chow cohomology through the rational Chern character. It also records the
canonical rational extension of the cohomological Chern character and its diagonal grading. -/
structure RationalChernCharacterComparison
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w}) (dimension : C → ℕ)
    (CH₀ : C → Type x) [∀ X, CommRing (CH₀ X)]
    (CHgradeZ : ∀ X, ℤ → Submodule ℤ (CH₀ X)) [∀ X, GradedAlgebra (CHgradeZ X)]
    (cyclePullback : ∀ {X Y : C}, (X ⟶ Y) → CHgradeZ Y →ₐᵍ[ℤ] CHgradeZ X)
    (CH : Cᵒᵖ ⥤ RingCat.{y}) (H : Cᵒᵖ ⥤ RingCat.{z})
    (CHgrade : ∀ X, ℕ → Submodule ℤ (CH.obj (Opposite.op X)))
    (Hdiag : ∀ X, ℕ → Submodule ℤ (H.obj (Opposite.op X)))
    [∀ X, GradedAlgebra (CHgrade X)] [∀ X, GradedAlgebra (Hdiag X)]
    [∀ X, Algebra ℚ (CH.obj (Opposite.op X))]
    [∀ X, Algebra ℚ (H.obj (Opposite.op X))]
    (chCH : ∀ X, Scheme.VectorBundleK0 (toScheme.obj X) →+*
      PowerSeries (CH.obj (Opposite.op X)))
    (chH : ∀ X, Scheme.VectorBundleK0 (toScheme.obj X) →+*
      PowerSeries (H.obj (Opposite.op X))) where
  /-- The chosen model identifies the rationalization of the integral Chow ring with `CH`. -/
  chowModel : ∀ X, RationalChow CH₀ X ≃+* CH.obj (Opposite.op X)
  /-- The rational Chern character identifies rationalized vector-bundle `K₀` with rational
  Chow cohomology. -/
  chowEquiv : ∀ X, RationalK0 toScheme X ≃+* RationalChow CH₀ X
  /-- The Chow model identifies the rationalized integral grading with the grading on `CH`. -/
  chowModel_grade : ∀ X i (z : RationalChow CH₀ X),
    z ∈ RationalChow.grade CH₀ CHgradeZ X i ↔ chowModel X z ∈ CHgrade X i
  /-- The rational Chow model commutes with pullback. -/
  chowModel_naturality : ∀ {X Y : C} (f : X ⟶ Y) (z : RationalChow CH₀ Y),
    chowModel X (RationalChow.pullback CH₀ CHgradeZ cyclePullback f z) =
      CH.map f.op (chowModel Y z)
  /-- The rational Chern-character equivalence commutes with pullback. -/
  chowEquiv_naturality : ∀ {X Y : C} (f : X ⟶ Y) (alpha : RationalK0 toScheme Y),
    chowEquiv X (RationalK0.pullback toScheme f alpha) =
      RationalChow.pullback CH₀ CHgradeZ cyclePullback f (chowEquiv Y alpha)
  /-- Every coefficient of the rational extension of the Chow Chern character is homogeneous. -/
  chowCharacter_coeff_mem : ∀ X (alpha : RationalK0 toScheme X) i,
    PowerSeries.coeff i (RationalK0.extend toScheme (chCH X) alpha) ∈ CHgrade X i
  /-- The finite total of the rational Chow Chern character is the specified equivalence. -/
  chowCharacter_total : ∀ X (alpha : RationalK0 toScheme X),
    ∑ i ∈ Finset.range (dimension X + 1),
        PowerSeries.coeff i (RationalK0.extend toScheme (chCH X) alpha) =
      chowModel X (chowEquiv X alpha)
  /-- The rational extension of the Chow Chern character commutes with pullback. -/
  chowCharacter_naturality : ∀ {X Y : C} (f : X ⟶ Y) (alpha : RationalK0 toScheme Y),
    PowerSeries.map (CH.map f.op).hom (RationalK0.extend toScheme (chCH Y) alpha) =
      RationalK0.extend toScheme (chCH X) (RationalK0.pullback toScheme f alpha)
  /-- Every coefficient of the rational extension of the cohomological Chern character lies in
  the diagonal grading. -/
  cohomologyCharacter_coeff_mem : ∀ X (alpha : RationalK0 toScheme X) i,
    PowerSeries.coeff i (RationalK0.extend toScheme (chH X) alpha) ∈ Hdiag X i
  /-- The rational extension of the cohomological Chern character commutes with pullback. -/
  cohomologyCharacter_naturality : ∀ {X Y : C} (f : X ⟶ Y)
      (alpha : RationalK0 toScheme Y),
    PowerSeries.map (H.map f.op).hom (RationalK0.extend toScheme (chH Y) alpha) =
      RationalK0.extend toScheme (chH X) (RationalK0.pullback toScheme f alpha)

namespace RationalChernCharacterComparison

/-- Build a rational Chern-character comparison from its two equivalences and their grading,
pullback, coefficient, and finite-total laws. -/
def ofLaws
    {C : Type u} [Category.{v} C] {toScheme : C ⥤ Scheme.{w}} {dimension : C → ℕ}
    {CH₀ : C → Type x} [∀ X, CommRing (CH₀ X)]
    {CHgradeZ : ∀ X, ℤ → Submodule ℤ (CH₀ X)} [∀ X, GradedAlgebra (CHgradeZ X)]
    {cyclePullback : ∀ {X Y : C}, (X ⟶ Y) → CHgradeZ Y →ₐᵍ[ℤ] CHgradeZ X}
    {CH : Cᵒᵖ ⥤ RingCat.{y}} {H : Cᵒᵖ ⥤ RingCat.{z}}
    {CHgrade : ∀ X, ℕ → Submodule ℤ (CH.obj (Opposite.op X))}
    {Hdiag : ∀ X, ℕ → Submodule ℤ (H.obj (Opposite.op X))}
    [∀ X, GradedAlgebra (CHgrade X)] [∀ X, GradedAlgebra (Hdiag X)]
    [∀ X, Algebra ℚ (CH.obj (Opposite.op X))]
    [∀ X, Algebra ℚ (H.obj (Opposite.op X))]
    {chCH : ∀ X, Scheme.VectorBundleK0 (toScheme.obj X) →+*
      PowerSeries (CH.obj (Opposite.op X))}
    {chH : ∀ X, Scheme.VectorBundleK0 (toScheme.obj X) →+*
      PowerSeries (H.obj (Opposite.op X))}
    (chowModel : ∀ X, RationalChow CH₀ X ≃+* CH.obj (Opposite.op X))
    (chowEquiv : ∀ X, RationalK0 toScheme X ≃+* RationalChow CH₀ X)
    (chowModel_grade : ∀ X i (z : RationalChow CH₀ X),
      z ∈ RationalChow.grade CH₀ CHgradeZ X i ↔ chowModel X z ∈ CHgrade X i)
    (chowModel_naturality : ∀ {X Y : C} (f : X ⟶ Y) (z : RationalChow CH₀ Y),
      chowModel X (RationalChow.pullback CH₀ CHgradeZ cyclePullback f z) =
        CH.map f.op (chowModel Y z))
    (chowEquiv_naturality : ∀ {X Y : C} (f : X ⟶ Y) (alpha : RationalK0 toScheme Y),
      chowEquiv X (RationalK0.pullback toScheme f alpha) =
        RationalChow.pullback CH₀ CHgradeZ cyclePullback f (chowEquiv Y alpha))
    (chowCharacter_coeff_mem : ∀ X (alpha : RationalK0 toScheme X) i,
      PowerSeries.coeff i (RationalK0.extend toScheme (chCH X) alpha) ∈ CHgrade X i)
    (chowCharacter_total : ∀ X (alpha : RationalK0 toScheme X),
      ∑ i ∈ Finset.range (dimension X + 1),
          PowerSeries.coeff i (RationalK0.extend toScheme (chCH X) alpha) =
        chowModel X (chowEquiv X alpha))
    (chowCharacter_naturality : ∀ {X Y : C} (f : X ⟶ Y)
        (alpha : RationalK0 toScheme Y),
      PowerSeries.map (CH.map f.op).hom (RationalK0.extend toScheme (chCH Y) alpha) =
        RationalK0.extend toScheme (chCH X) (RationalK0.pullback toScheme f alpha))
    (cohomologyCharacter_coeff_mem : ∀ X (alpha : RationalK0 toScheme X) i,
      PowerSeries.coeff i (RationalK0.extend toScheme (chH X) alpha) ∈ Hdiag X i)
    (cohomologyCharacter_naturality : ∀ {X Y : C} (f : X ⟶ Y)
        (alpha : RationalK0 toScheme Y),
      PowerSeries.map (H.map f.op).hom (RationalK0.extend toScheme (chH Y) alpha) =
        RationalK0.extend toScheme (chH X) (RationalK0.pullback toScheme f alpha)) :
    RationalChernCharacterComparison toScheme dimension CH₀ CHgradeZ cyclePullback
      CH H CHgrade Hdiag chCH chH where
  chowModel := chowModel
  chowEquiv := chowEquiv
  chowModel_grade := chowModel_grade
  chowModel_naturality := chowModel_naturality
  chowEquiv_naturality := chowEquiv_naturality
  chowCharacter_coeff_mem := chowCharacter_coeff_mem
  chowCharacter_total := chowCharacter_total
  chowCharacter_naturality := chowCharacter_naturality
  cohomologyCharacter_coeff_mem := cohomologyCharacter_coeff_mem
  cohomologyCharacter_naturality := cohomologyCharacter_naturality

end RationalChernCharacterComparison

namespace CycleClass

/-- Extend an integral cycle-class map to the selected rational Chow model. -/
noncomputable def rationalApp
    {C : Type u} [Category.{v} C]
    {CH₀ : C → Type x} [∀ X, CommRing (CH₀ X)]
    {CHgradeZ : ∀ X, ℤ → Submodule ℤ (CH₀ X)}
    [∀ X, GradedAlgebra (CHgradeZ X)]
    {cyclePullback : ∀ {X Y : C}, (X ⟶ Y) → CHgradeZ Y →ₐᵍ[ℤ] CHgradeZ X}
    {H : Cᵒᵖ ⥤ RingCat.{z}} {Hdiag : ∀ X, ℕ → Submodule ℤ (H.obj (Opposite.op X))}
    [∀ X, Algebra ℚ (H.obj (Opposite.op X))]
    (gamma : CycleClass CH₀ CHgradeZ cyclePullback H Hdiag)
    (CH : Cᵒᵖ ⥤ RingCat.{y})
    (chowModel : ∀ X, RationalChow CH₀ X ≃+* CH.obj (Opposite.op X)) (X : C) :
    CH.obj (Opposite.op X) →+* H.obj (Opposite.op X) :=
  (RationalChow.extend CH₀ (gamma.app X).toRingHom).comp
    (chowModel X).symm.toRingHom

/-- Chern-character compatibility for the rational extension of an integral cycle-class
rule. -/
def FactorsChernCharacter
    {C : Type u} [Category.{v} C] {toScheme : C ⥤ Scheme.{w}}
    {CH₀ : C → Type x} [∀ X, CommRing (CH₀ X)]
    {CHgradeZ : ∀ X, ℤ → Submodule ℤ (CH₀ X)}
    [∀ X, GradedAlgebra (CHgradeZ X)]
    {cyclePullback : ∀ {X Y : C}, (X ⟶ Y) → CHgradeZ Y →ₐᵍ[ℤ] CHgradeZ X}
    {CH : Cᵒᵖ ⥤ RingCat.{y}} {H : Cᵒᵖ ⥤ RingCat.{z}}
    {Hdiag : ∀ X, ℕ → Submodule ℤ (H.obj (Opposite.op X))}
    [∀ X, Algebra ℚ (H.obj (Opposite.op X))]
    (gamma : CycleClass CH₀ CHgradeZ cyclePullback H Hdiag)
    (chowModel : ∀ X, RationalChow CH₀ X ≃+* CH.obj (Opposite.op X))
    (chCH : ∀ X, Scheme.VectorBundleK0 (toScheme.obj X) →+*
      PowerSeries (CH.obj (Opposite.op X)))
    (chH : ∀ X, Scheme.VectorBundleK0 (toScheme.obj X) →+*
      PowerSeries (H.obj (Opposite.op X))) : Prop :=
  ∀ X alpha, PowerSeries.map (gamma.rationalApp CH chowModel X) (chCH X alpha) = chH X alpha

/-- Coefficientwise form of Chern-character compatibility. -/
theorem character_coeff
    {C : Type u} [Category.{v} C] {toScheme : C ⥤ Scheme.{w}}
    {CH₀ : C → Type x} [∀ X, CommRing (CH₀ X)]
    {CHgradeZ : ∀ X, ℤ → Submodule ℤ (CH₀ X)}
    [∀ X, GradedAlgebra (CHgradeZ X)]
    {cyclePullback : ∀ {X Y : C}, (X ⟶ Y) → CHgradeZ Y →ₐᵍ[ℤ] CHgradeZ X}
    {CH : Cᵒᵖ ⥤ RingCat.{y}} {H : Cᵒᵖ ⥤ RingCat.{z}}
    {Hdiag : ∀ X, ℕ → Submodule ℤ (H.obj (Opposite.op X))}
    [∀ X, Algebra ℚ (H.obj (Opposite.op X))]
    (gamma : CycleClass CH₀ CHgradeZ cyclePullback H Hdiag)
    (chowModel : ∀ X, RationalChow CH₀ X ≃+* CH.obj (Opposite.op X))
    (chCH : ∀ X, Scheme.VectorBundleK0 (toScheme.obj X) →+*
      PowerSeries (CH.obj (Opposite.op X)))
    (chH : ∀ X, Scheme.VectorBundleK0 (toScheme.obj X) →+*
      PowerSeries (H.obj (Opposite.op X)))
    (h : gamma.FactorsChernCharacter chowModel chCH chH)
    (X : C) (alpha : Scheme.VectorBundleK0 (toScheme.obj X)) (i : ℕ) :
    gamma.rationalApp CH chowModel X (PowerSeries.coeff i (chCH X alpha)) =
      PowerSeries.coeff i (chH X alpha) := sorry

end CycleClass

end WeilCohomology
