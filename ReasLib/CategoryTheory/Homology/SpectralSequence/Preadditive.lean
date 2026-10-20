/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preadditive structure on spectral sequences

Morphisms of spectral sequences form additive groups by adding their page maps componentwise.
This owner is independent of any particular page restriction, so page-level functors can reuse
the same preadditive structure without rebuilding operations locally.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory
namespace SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type w} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

section Morphisms

variable {E E' : SpectralSequence C c r₀}

namespace Hom

/-! The explicit proof argument in `pageMap` is intentional: the underlying mathlib field has a
default lower-bound proof, but a family of page maps must quantify over that proof explicitly. -/

/-- The pagewise map of a spectral-sequence morphism, with its lower-bound proof explicit. -/
abbrev pageMap (f : E ⟶ E') :
    ∀ r : {r : ℤ // r₀ ≤ r}, E.page r.1 r.2 ⟶ E'.page r.1 r.2 :=
  fun r ↦ f.hom r.1 r.2

/-- The explicit page-map projection is injective. -/
@[stacks 00ZY "spectral-sequence morphism extensionality through explicit page maps"]
theorem pageMap_injective : Function.Injective (pageMap (E := E) (E' := E')) := sorry

/-- Zero morphisms of spectral sequences have zero map on every page. -/
@[stacks 00ZY "zero spectral-sequence morphism"]
instance homZero : Zero (E ⟶ E') where
  zero :=
    { hom := fun _ _ ↦ 0
      comm := sorry }

/-- Addition of spectral-sequence morphisms is defined pagewise. -/
@[stacks 00ZY "addition of spectral-sequence morphisms"]
instance homAdd : Add (E ⟶ E') where
  add f g :=
    { hom := fun r hr ↦ f.hom r hr + g.hom r hr
      comm := sorry }

/-- Negation of a spectral-sequence morphism is defined pagewise. -/
@[stacks 00ZY "negation of spectral-sequence morphisms"]
instance homNeg : Neg (E ⟶ E') where
  neg f :=
    { hom := fun r hr ↦ -f.hom r hr
      comm := sorry }

/-- Subtraction of spectral-sequence morphisms is defined pagewise. -/
@[stacks 00ZY "subtraction of spectral-sequence morphisms"]
instance homSub : Sub (E ⟶ E') where
  sub f g :=
    { hom := fun r hr ↦ f.hom r hr - g.hom r hr
      comm := sorry }

/-- Natural-number scalar multiplication of spectral-sequence morphisms is pagewise. -/
@[stacks 00ZY "natural scalar multiplication of spectral-sequence morphisms"]
instance homNatSMul : SMul ℕ (E ⟶ E') where
  smul n f :=
    { hom := fun r hr ↦ n • f.hom r hr
      comm := sorry }

/-- Integer scalar multiplication of spectral-sequence morphisms is pagewise. -/
@[stacks 00ZY "integer scalar multiplication of spectral-sequence morphisms"]
instance homIntSMul : SMul ℤ (E ⟶ E') where
  smul n f :=
    { hom := fun r hr ↦ n • f.hom r hr
      comm := sorry }

/-- The page-map projection is injective on spectral-sequence morphisms. -/
@[stacks 00ZY "spectral-sequence morphism extensionality through page maps"]
theorem hom_injective :
    Function.Injective (fun f : E ⟶ E' => pageMap (E := E) (E' := E') f) :=
  pageMap_injective (E := E) (E' := E')

/-- The page-map projection of a zero spectral-sequence morphism is zero. -/
@[simp, stacks 00ZY "zero spectral-sequence page map"]
theorem zero_hom (r : ℤ) (hr : r₀ ≤ r) : (0 : E ⟶ E').hom r hr = 0 := sorry

/-- The page-map projection of a sum of spectral-sequence morphisms is the pagewise sum. -/
@[simp, stacks 00ZY "sum of spectral-sequence page maps"]
theorem add_hom (f g : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) :
    (f + g).hom r hr = f.hom r hr + g.hom r hr := sorry

/-- The page-map projection of a negated spectral-sequence morphism is pagewise negation. -/
@[simp, stacks 00ZY "negation of spectral-sequence page maps"]
theorem neg_hom (f : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) :
    (-f).hom r hr = -f.hom r hr := sorry

/-- The page-map projection of a difference of spectral-sequence morphisms is pagewise subtraction. -/
@[simp, stacks 00ZY "difference of spectral-sequence page maps"]
theorem sub_hom (f g : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) :
    (f - g).hom r hr = f.hom r hr - g.hom r hr := sorry

/-- Natural-number scalar multiplication commutes with the page-map projection. -/
@[simp, stacks 00ZY "natural scalar action on spectral-sequence page maps"]
theorem nsmul_hom (n : ℕ) (f : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) :
    (n • f).hom r hr = n • f.hom r hr := sorry

/-- Integer scalar multiplication commutes with the page-map projection. -/
@[simp, stacks 00ZY "integer scalar action on spectral-sequence page maps"]
theorem zsmul_hom (n : ℤ) (f : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) :
    (n • f).hom r hr = n • f.hom r hr := sorry

/-- Spectral-sequence morphisms form an additive commutative group componentwise. -/
@[stacks 00ZY "additive group of spectral-sequence morphisms"]
instance homAddCommGroup : AddCommGroup (E ⟶ E') :=
  Function.Injective.addCommGroup
    (fun f : E ⟶ E' ↦ pageMap (E := E) (E' := E') f)
    (hom_injective (E := E) (E' := E'))
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl)

end Hom

end Morphisms

/-- The category of spectral sequences is preadditive when the coefficient category is abelian. -/
@[stacks 00ZY "preadditive category of spectral sequences"]
instance : Preadditive (SpectralSequence C c r₀) where
  homGroup := fun E E' ↦ inferInstance
  add_comp := sorry
  comp_add := sorry

#synth Preadditive (SpectralSequence C c r₀)

end SpectralSequence
end CategoryTheory
