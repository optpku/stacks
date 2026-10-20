/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite type for finite ring pullbacks

This file records the finite-family pullback criterion for finite-type algebras.  The canonical
core omits the redundant finite-type hypotheses on the common quotient factors, while the
source-facing companion retains them.
-/

open CategoryTheory.Limits CommRingCat

universe u

namespace CategoryTheory.IsPullback

section Core

variable {ι R P Q : Type u} {A B : ι → Type u}
variable [Finite ι] [CommRing R] [CommRing P] [CommRing Q]
variable [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
variable [Algebra R P] [Algebra R Q]
variable [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)]

/-- A pullback of a finite family of surjective finite-type algebra maps is finite type.  Finite
type of the common quotient factors follows from the surjections out of `Q`. -/
@[stacks 08NI "finite-family pullback core"]
theorem finiteType_pi_of_surjective
    [IsNoetherianRing R] [Algebra.FiniteType R Q]
    [∀ i, Algebra.FiniteType R (A i)]
    (φ : ∀ i, A i →ₐ[R] B i) (ψ : ∀ i, Q →ₐ[R] B i)
    (f : P →ₐ[R] Q) (g : P →ₐ[R] ∀ i, A i)
    (hφ : ∀ i, Function.Surjective (φ i))
    (hψ : ∀ i, Function.Surjective (ψ i))
    (hcart : IsPullback (ofHom f.toRingHom) (ofHom g.toRingHom)
      (ofHom (AlgHom.pi ψ).toRingHom)
      (ofHom (AlgHom.pi fun i ↦ (φ i).comp (Pi.evalAlgHom R A i)).toRingHom)) :
    Algebra.FiniteType R P := sorry

variable [hB : ∀ i, Algebra.FiniteType R (B i)]

include hB in
/-- In a cartesian square over a finite family, if both families of maps are
surjective and `Q`, every `A i`, and every `B i` are finite type over the Noetherian base `R`,
then the pullback ring `P` is finite type over `R`. -/
@[stacks 08NI "finite-type finite-family pullback"]
theorem finiteType_pi_of_surjective_of_finiteType
    [IsNoetherianRing R] [Algebra.FiniteType R Q]
    [∀ i, Algebra.FiniteType R (A i)]
    (φ : ∀ i, A i →ₐ[R] B i) (ψ : ∀ i, Q →ₐ[R] B i)
    (f : P →ₐ[R] Q) (g : P →ₐ[R] ∀ i, A i)
    (hφ : ∀ i, Function.Surjective (φ i))
    (hψ : ∀ i, Function.Surjective (ψ i))
    (hcart : IsPullback (ofHom f.toRingHom) (ofHom g.toRingHom)
      (ofHom (AlgHom.pi ψ).toRingHom)
      (ofHom (AlgHom.pi fun i ↦ (φ i).comp (Pi.evalAlgHom R A i)).toRingHom)) :
    Algebra.FiniteType R P := sorry

end Core

end CategoryTheory.IsPullback

namespace AlgHom

section Binary

variable {R A B C : Type u}
variable [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/-- The fiber product of a surjective finite-type algebra map and a finite algebra map is finite
type over a Noetherian base.  Finite type of the common target follows from surjectivity. -/
@[stacks 00IT "binary fiber-product finite-type core"]
theorem finiteType_fiberProduct_of_surjective_of_finite
    [IsNoetherianRing R] [Algebra.FiniteType R A] [Algebra.FiniteType R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B)
    (hf : Function.Surjective f) (hg : g.Finite) :
    Algebra.FiniteType R
      (equalizer (f.comp (fst R A C)) (g.comp (snd R A C))) := sorry

variable [hB : Algebra.FiniteType R B]

include hB in
/-- If `R` is Noetherian, `A`, `B`, and `C` are finite type over `R`, the map
`A → B` is surjective, and `B` is finite over `C`, then `A ×_B C` is finite type over `R`. -/
@[stacks 00IT "finite-type binary fiber product"]
theorem finiteType_fiberProduct_of_surjective_of_finiteType
    [IsNoetherianRing R] [Algebra.FiniteType R A] [Algebra.FiniteType R C]
    (f : A →ₐ[R] B) (g : C →ₐ[R] B)
    (hf : Function.Surjective f) (hg : g.Finite) :
    Algebra.FiniteType R
      (equalizer (f.comp (fst R A C)) (g.comp (snd R A C))) := sorry

end Binary

end AlgHom
