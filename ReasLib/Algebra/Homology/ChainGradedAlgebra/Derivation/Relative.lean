/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ChainGradedAlgebra.Derivation
public import ReasLib.Algebra.Homology.ChainGradedAlgebra.Hom
public import ReasLib.LinearAlgebra.Quotient.Descent

/-!
# Relative derivations of chain-graded algebras

A relative graded derivation along `q : A ⟶ B` is a homogeneous linear map from `A` to `B`
whose Leibniz rule uses the `A`-module structure on `B` induced by `q`.  This is the graded
counterpart of mathlib's `Derivation R A M` and is the correct owner for derivations before and
after descent through a surjective graded-algebra homomorphism.
-/

@[expose] public section

noncomputable section

universe u v

variable {R : Type u} [CommRing R]

namespace ChainGradedAlgebra

variable (A B : ChainGradedAlgebra.{u, v} R) (k : ℤ)

/-- A degree-`k` homogeneous linear map from one chain-graded algebra to another. -/
@[stacks 09PS "infrastructure: relative homogeneous maps"]
abbrev HomogeneousMapTo :=
  ∀ i : ℤ, A.X i →ₗ[R] B.X (i + k)

/-- The graded Leibniz predicate for a homogeneous map with values along a graded-algebra
homomorphism. -/
@[stacks 09PS "infrastructure: relative graded Leibniz rule"]
def SatisfiesLeibnizAlong {A B : ChainGradedAlgebra.{u, v} R}
    (q : Hom A B) (k : ℤ) (D : HomogeneousMapTo A B k) : Prop :=
  ∀ i j : ℤ, ∀ a : A.X i, ∀ b : A.X j,
    D (i + j) (A.mul i j a b) =
      B.reindex (add_right_comm i k j)
          (B.mul (i + k) j (D i a) (q j b)) +
        (k * i).negOnePow •
          B.reindex (add_assoc i j k).symm
            (B.mul i (j + k) (q i a) (D j b))

/-- A degree-`k` graded derivation with values along `q`. -/
@[stacks 09PS "infrastructure: derivations along graded homomorphisms"]
structure DerivationAlong {A B : ChainGradedAlgebra.{u, v} R}
    (q : Hom A B) (k : ℤ) where
  /-- The underlying degree-`k` homogeneous linear map. -/
  toHomogeneousMap : HomogeneousMapTo A B k
  /-- The relative graded Leibniz rule. -/
  leibniz : SatisfiesLeibnizAlong q k toHomogeneousMap

namespace DerivationAlong

variable {A B : ChainGradedAlgebra.{u, v} R} {q : Hom A B} {k : ℤ}

/-- A relative graded derivation acts on each homogeneous component. -/
instance instCoeFun : CoeFun (DerivationAlong q k)
    (fun _ ↦ ∀ i : ℤ, A.X i → B.X (i + k)) where
  coe D := fun i x ↦ toHomogeneousMap D i x

/-- Evaluation of a relative derivation is evaluation of its underlying homogeneous map. -/
@[simp]
theorem coe_apply (D : DerivationAlong q k) (i : ℤ) (x : A.X i) :
    D i x = toHomogeneousMap D i x := sorry

/-- A relative graded derivation satisfies the relative graded Leibniz rule. -/
theorem satisfiesLeibniz (D : DerivationAlong q k) :
    SatisfiesLeibnizAlong q k (toHomogeneousMap D) := sorry

/-- The homogeneous endomorphism obtained by descending a relative derivation degreewise through
a surjective graded-algebra homomorphism. -/
@[stacks 09PS "infrastructure: descent of relative graded derivations"]
def descendMap (D : DerivationAlong q k)
    (hq : ∀ i, Function.Surjective (q.map i))
    (hker : ∀ i, LinearMap.ker (q.map i) ≤ LinearMap.ker (toHomogeneousMap D i)) :
    HomogeneousMap B k :=
  fun i ↦ LinearMap.descendOfSurjective (q.map i) (hq i)
    (toHomogeneousMap D i) (hker i)

/-- The descended homogeneous family factors the relative derivation through the given
surjection. -/
@[simp]
theorem descendMap_comp (D : DerivationAlong q k)
    (hq : ∀ i, Function.Surjective (q.map i))
    (hker : ∀ i, LinearMap.ker (q.map i) ≤ LinearMap.ker (toHomogeneousMap D i))
    (i : ℤ) :
    (descendMap D hq hker i).comp (q.map i) = toHomogeneousMap D i := sorry

/-- The descended homogeneous family satisfies the endomorphism graded Leibniz rule. -/
theorem descendMap_leibniz (D : DerivationAlong q k)
    (hq : ∀ i, Function.Surjective (q.map i))
    (hker : ∀ i, LinearMap.ker (q.map i) ≤ LinearMap.ker (toHomogeneousMap D i)) :
    SatisfiesLeibniz B k (descendMap D hq hker) := sorry

/-- A relative graded derivation that kills the kernel of a degreewise-surjective homomorphism
descends canonically to the target. -/
@[stacks 09PS "infrastructure: descended graded derivation"]
def descend (D : DerivationAlong q k)
    (hq : ∀ i, Function.Surjective (q.map i))
    (hker : ∀ i, LinearMap.ker (q.map i) ≤ LinearMap.ker (toHomogeneousMap D i)) :
    Derivation B k :=
  ⟨descendMap D hq hker, descendMap_leibniz D hq hker⟩

/-- The descended derivation sends the image of a representative to the value of the relative
derivation on that representative. -/
@[simp]
theorem descend_apply (D : DerivationAlong q k)
    (hq : ∀ i, Function.Surjective (q.map i))
    (hker : ∀ i, LinearMap.ker (q.map i) ≤ LinearMap.ker (toHomogeneousMap D i))
    (i : ℤ) (x : A.X i) :
    descend D hq hker i (q i x) = D i x := sorry

/-- The descended derivation is uniquely determined by its values on representatives. -/
theorem eq_descend (D : DerivationAlong q k)
    (hq : ∀ i, Function.Surjective (q.map i))
    (hker : ∀ i, LinearMap.ker (q.map i) ≤ LinearMap.ker (toHomogeneousMap D i))
    (E : Derivation B k) (hE : ∀ i x, E i (q i x) = D i x) :
    E = descend D hq hker := sorry

end DerivationAlong

namespace Derivation

variable {A B : ChainGradedAlgebra.{u, v} R} {k : ℤ}

/-- Precomposition of an endoderivation with a graded-algebra homomorphism, as a relative
homogeneous map. -/
def alongMap (q : Hom A B) (D : Derivation B k) : HomogeneousMapTo A B k :=
  fun i ↦ (toHomogeneousMap D i).comp (q.map i)

/-- Precomposition of an endoderivation with a graded-algebra homomorphism satisfies the relative
graded Leibniz rule. -/
theorem alongMap_leibniz (q : Hom A B) (D : Derivation B k) :
    SatisfiesLeibnizAlong q k (alongMap q D) := sorry

/-- An endoderivation of the target, regarded as a derivation along a graded-algebra
homomorphism. -/
def along (q : Hom A B) (D : Derivation B k) : DerivationAlong q k :=
  ⟨alongMap q D, alongMap_leibniz q D⟩

/-- A derivation regarded along a homomorphism acts by first applying the homomorphism. -/
@[simp]
theorem along_apply (q : Hom A B) (D : Derivation B k) (i : ℤ) (x : A.X i) :
    along q D i x = D i (q i x) := sorry

end Derivation

end ChainGradedAlgebra
