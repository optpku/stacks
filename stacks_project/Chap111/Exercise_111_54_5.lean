/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.FiniteBirational
import StacksCheckRecall

/-!
# Exercise 111.54.5

For a field `k` and a finite birational morphism `π : X ⟶ Y` of curves over `k`
with `X` projective and nonsingular, `Y` is proper, `π` is the normalization of
`Y`, and some dense open `V ⊆ Y` has `π.left ∣_ V` an isomorphism. The exercise
produces an ample effective Cartier divisor on the isomorphism open, pushes it
forward to `Y`, and compares global sections of the corresponding twists via the
cokernel of `𝒪_Y ⟶ π_* 𝒪_X`.

Over the affine spectrum of a field, projectivity of `X.hom` is equivalently
expressed by `IsProper X.hom` together with
`Scheme.Modules.HasAmpleInvertibleModule X.left`. The shared statements retain
both intrinsic hypotheses, as well as regularity and the finite birational map.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.IdealSheafData
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

/- The finite birational projective-curve setup implies properness of the target. -/
#check (AlgebraicGeometry.Curve.FiniteBirational.targetIsProper :
  ∀ {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left], IsProper Y.hom)

/- The given morphism identifies the source with the actual normalization of the target. -/
#check (AlgebraicGeometry.Curve.FiniteBirational.existsNormalizationIso :
  ∀ {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left],
    ∃ e : X.left ≅ Y.left.normalization, e.hom ≫ Y.left.normalizationTo = π.left)

/- Exercise 111.54.5 (1): an ample effective Cartier divisor exists inside the
full inverse image of the dense isomorphism open. -/
@[stacks 06A4] #check (AlgebraicGeometry.Curve.FiniteBirational.existsAmpleDivisor :
  ∀ {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left]
    {V : Y.left.Opens} (hV : Dense (V : Set Y.left)) (hiso : IsIso (π.left ∣_ V)),
    ∃ (D : X.left.IdealSheafData) (hD : IsEffectiveCartierDivisor D.subschemeι),
      (D.support : Set X.left) ⊆ (π.left ⁻¹ᵁ V : Set X.left) ∧
        isAmpleObject (associatedSheaf D (hD := hD)))

/- Exercise 111.54.5 (2): the scheme-theoretic image `D.map π.left` is an
effective Cartier divisor on the target. -/
@[stacks 06A4] #check (AlgebraicGeometry.Curve.FiniteBirational.imageIsEffectiveCartier :
  ∀ {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left]
    {V : Y.left.Opens} (hV : Dense (V : Set Y.left)) (hiso : IsIso (π.left ∣_ V))
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (hDU : (D.support : Set X.left) ⊆ (π.left ⁻¹ᵁ V : Set X.left)),
    IsEffectiveCartierDivisor (D.map π.left).subschemeι)

/- Exercise 111.54.5 (3): the actual structure-module map has coherent cokernel. -/
@[stacks 06A4] #check (AlgebraicGeometry.Curve.FiniteBirational.cokernelIsCoherent :
  ∀ {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left],
    (Limits.cokernel
      (SheafOfModules.unitToPushforwardObjUnit π.left.toRingCatSheafHom)).IsCoherent)

/- Exercise 111.54.5 (4): the same cokernel is supported in the complement
of the dense isomorphism open. -/
@[stacks 06A4] #check (AlgebraicGeometry.Curve.FiniteBirational.cokernelSupport_subset :
  ∀ {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left]
    {V : Y.left.Opens} (hV : Dense (V : Set Y.left)) (hiso : IsIso (π.left ∣_ V)),
    RingedSpace.moduleSupport
      (Limits.cokernel
        (SheafOfModules.unitToPushforwardObjUnit π.left.toRingCatSheafHom)) ⊆
      (V : Set Y.left)ᶜ)

/- Exercise 111.54.5 (5): every integral twist admits a monomorphism with
cokernel isomorphic to the fixed structure-module cokernel. -/
@[stacks 06A4] #check (AlgebraicGeometry.Curve.FiniteBirational.existsTwistMap :
  ∀ {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left]
    {V : Y.left.Opens} (hV : Dense (V : Set Y.left)) (hiso : IsIso (π.left ∣_ V))
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (hDU : (D.support : Set X.left) ⊆ (π.left ⁻¹ᵁ V : Set X.left))
    [IsEffectiveCartierDivisor (D.map π.left).subschemeι] (n : ℤ),
    ∃ φ : tensorPowerInt (associatedSheaf (D.map π.left)) n ⟶
        (Scheme.Modules.pushforward π.left).obj (tensorPowerInt (associatedSheaf D) n),
      Mono φ ∧ IsIsomorphic (Limits.cokernel φ)
        (Limits.cokernel
          (SheafOfModules.unitToPushforwardObjUnit π.left.toRingCatSheafHom)))

/- Exercise 111.54.5 (6): the signed global-section dimension difference is
nonnegative and bounded above by `dim_k H⁰(Y, Q)`. -/
@[stacks 06A4] #check (AlgebraicGeometry.Curve.FiniteBirational.h0DifferenceBounds :
  ∀ {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left]
    {V : Y.left.Opens} (hV : Dense (V : Set Y.left)) (hiso : IsIso (π.left ∣_ V))
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (hDU : (D.support : Set X.left) ⊆ (π.left ⁻¹ᵁ V : Set X.left))
    [IsEffectiveCartierDivisor (D.map π.left).subschemeι] (n : ℤ),
    0 ≤ (X.hom.cohomologyFinrank (tensorPowerInt (associatedSheaf D) n) 0 : ℤ) -
        (Y.hom.cohomologyFinrank
          (tensorPowerInt (associatedSheaf (D.map π.left)) n) 0 : ℤ) ∧
      (X.hom.cohomologyFinrank (tensorPowerInt (associatedSheaf D) n) 0 : ℤ) -
          (Y.hom.cohomologyFinrank
            (tensorPowerInt (associatedSheaf (D.map π.left)) n) 0 : ℤ) ≤
        (Y.hom.cohomologyFinrank
          (Limits.cokernel
            (SheafOfModules.unitToPushforwardObjUnit π.left.toRingCatSheafHom)) 0 : ℤ))

/- Exercise 111.54.5 (7): ampleness on the source implies arbitrarily large
spaces of global sections on the target for all sufficiently large natural twists. -/
@[stacks 06A4] #check (AlgebraicGeometry.Curve.FiniteBirational.eventuallyH0Ge :
  ∀ {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Curve X] [Curve Y] [IsProper X.hom] [Scheme.Regular X.left]
    (hXample : Scheme.Modules.HasAmpleInvertibleModule X.left)
    (π : X ⟶ Y) [IsFinite π.left] [IsBirational π.left]
    {V : Y.left.Opens} (hV : Dense (V : Set Y.left)) (hiso : IsIso (π.left ∣_ V))
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (hDU : (D.support : Set X.left) ⊆ (π.left ⁻¹ᵁ V : Set X.left))
    (hD_ample : isAmpleObject (associatedSheaf D))
    [IsEffectiveCartierDivisor (D.map π.left).subschemeι] (N : ℕ),
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      N ≤ Y.hom.cohomologyFinrank
        (tensorPowerInt (associatedSheaf (D.map π.left)) (n : ℤ)) 0)
