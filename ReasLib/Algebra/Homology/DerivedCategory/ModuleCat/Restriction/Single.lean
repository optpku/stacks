/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Single objects and derived restriction

This leaf exposes the objectwise comparison between restriction of scalars and the single-object
functor in any degree.  The comparison is the component of Mathlib's canonical
`mapDerivedCategorySingleFunctor`; no chapter-specific localization data is built here.

@stack 0BYX
@stack 091R
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.ModuleCat.RestrictScalars

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- The identity-on-carriers linear map from the restricted regular `B`-module to `B`. -/
@[stacks 091R "restricted regular module map"]
noncomputable def regularMap :
    (((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) : ModuleCat A) →ₗ[A] B :=
  { toFun := fun b ↦ b
    map_add' := by
      intro x y
      rfl
    map_smul' := by
      intro r x
      rw [ModuleCat.restrictScalars.smul_def]
      simpa using (algebraMap_smul B r (show B from x)) }

/-- The carrier-level formula for `regularMap`. -/
@[stacks 091R "restricted regular module map evaluation"]
theorem regularMap_apply (b : B) : regularMap (A := A) (B := B) b = b := rfl

/-- The identity-on-carriers map underlying the restricted regular module is bijective. -/
@[stacks 091R "restricted regular module map bijectivity"]
theorem regularMap_bijective : Function.Bijective (regularMap (A := A) (B := B)) := by
  constructor
  · intro x y h
    exact h
  · intro x
    exact ⟨x, rfl⟩

/-- The canonical linear equivalence between the restricted regular `B`-module and `B`. -/
@[stacks 091R "restricted regular module equivalence"]
noncomputable def regularEquiv :
    (((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) : ModuleCat A) ≃ₗ[A] B :=
  LinearEquiv.ofBijective (regularMap (A := A) (B := B))
    (regularMap_bijective (A := A) (B := B))

/-- The restricted-regular equivalence is the identity on the underlying carrier. -/
@[stacks 091R "restricted regular module equivalence evaluation"]
theorem regularEquiv_apply (b : B) : regularEquiv (A := A) (B := B) b = b := rfl

/-- The linear-map projection of `regularEquiv` is the explicit carrier map. -/
@[stacks 091R "restricted regular module equivalence map projection"]
theorem regularEquiv_toLinearMap :
    (regularEquiv (A := A) (B := B)).toLinearMap = regularMap (A := A) (B := B) := rfl

end CategoryTheory.ModuleCat.RestrictScalars

namespace CategoryTheory.ModuleCat.DerivedRestriction

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Restriction of scalars commutes with the single-object functor in degree `n`. -/
@[stacks 0BYX "single-object comparison for derived restriction"]
noncomputable abbrev singleIso (σ : R →+* S) (n : ℤ) (M : ModuleCat S) :
    ((ModuleCat.restrictScalars σ).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat S) n).obj M)) ≅
      (DerivedCategory.singleFunctor (ModuleCat R) n).obj
        ((ModuleCat.restrictScalars σ).obj M) :=
  ((ModuleCat.restrictScalars σ).mapDerivedCategorySingleFunctor n).app M

end CategoryTheory.ModuleCat.DerivedRestriction
