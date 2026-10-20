/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullbacks of linear maps

The pullback of `f : M -> P` and `g : N -> P` is the submodule of pairs `(m, n)` satisfying
`f m = g n`. This file provides its two projections and the elementwise universal property.
Unlike a presentation as the kernel of `(f, -g)`, this construction works over semirings and
does not choose a sign convention.

@stack 0H7M
-/

@[expose] public section

universe u v w x y

namespace LinearMap

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]
variable {P : Type x} [AddCommMonoid P] [Module R P]

/-- The pullback of two linear maps, realized as the submodule of compatible pairs. -/
@[stacks 0H7M "pullback of linear maps"]
def pullback (f : M →ₗ[R] P) (g : N →ₗ[R] P) : Submodule R (M × N) where
  carrier := {p | f p.1 = g p.2}
  zero_mem' := by simp
  add_mem' := by
    rintro ⟨m, n⟩ ⟨m', n'⟩ hm hn
    change f (m + m') = g (n + n')
    rw [map_add, map_add, hm, hn]
  smul_mem' := by
    rintro r ⟨m, n⟩ hmn
    change f (r • m) = g (r • n)
    rw [map_smul, map_smul, hmn]

@[simp]
theorem mem_pullback (f : M →ₗ[R] P) (g : N →ₗ[R] P) (m : M) (n : N) :
    (m, n) ∈ pullback f g ↔ f m = g n :=
  Iff.rfl

namespace Pullback

/-- The first projection from a linear-map pullback. -/
@[stacks 0H7M "first projection from a linear-map pullback"]
def fst (f : M →ₗ[R] P) (g : N →ₗ[R] P) : pullback f g →ₗ[R] M :=
  (LinearMap.fst R M N).domRestrict (pullback f g)

/-- The second projection from a linear-map pullback. -/
@[stacks 0H7M "second projection from a linear-map pullback"]
def snd (f : M →ₗ[R] P) (g : N →ₗ[R] P) : pullback f g →ₗ[R] N :=
  (LinearMap.snd R M N).domRestrict (pullback f g)

@[simp]
theorem fst_apply (f : M →ₗ[R] P) (g : N →ₗ[R] P) (p : pullback f g) :
    fst f g p = p.1.1 :=
  rfl

@[simp]
theorem snd_apply (f : M →ₗ[R] P) (g : N →ₗ[R] P) (p : pullback f g) :
    snd f g p = p.1.2 :=
  rfl

/-- The two projections from a pullback have equal composites. -/
@[stacks 0H7M "compatibility of linear-map pullback projections"]
theorem condition (f : M →ₗ[R] P) (g : N →ₗ[R] P) :
    f.comp (fst f g) = g.comp (snd f g) := by
  ext p
  exact p.property

variable {Q : Type y} [AddCommMonoid Q] [Module R Q]

/-- The universal map into a linear-map pullback. -/
@[stacks 0H7M "universal map into a linear-map pullback"]
def lift (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (u : Q →ₗ[R] M) (v : Q →ₗ[R] N) (h : f.comp u = g.comp v) :
    Q →ₗ[R] pullback f g :=
  (u.prod v).codRestrict (pullback f g) fun q => by
    rw [mem_pullback]
    exact LinearMap.congr_fun h q

@[simp]
theorem fst_comp_lift (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (u : Q →ₗ[R] M) (v : Q →ₗ[R] N) (h : f.comp u = g.comp v) :
    (fst f g).comp (lift f g u v h) = u :=
  rfl

@[simp]
theorem snd_comp_lift (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (u : Q →ₗ[R] M) (v : Q →ₗ[R] N) (h : f.comp u = g.comp v) :
    (snd f g).comp (lift f g u v h) = v :=
  rfl

/-- Linear maps into a pullback are determined by their two projections. -/
@[ext, stacks 0H7M "extensionality for linear-map pullbacks"]
theorem hom_ext (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    {u v : Q →ₗ[R] pullback f g}
    (hfst : (fst f g).comp u = (fst f g).comp v)
    (hsnd : (snd f g).comp u = (snd f g).comp v) : u = v := by
  apply LinearMap.ext
  intro q
  apply Subtype.ext
  apply Prod.ext
  · exact LinearMap.congr_fun hfst q
  · exact LinearMap.congr_fun hsnd q

/-- The first projection is surjective when the second defining map is surjective. -/
@[stacks 0H7M "surjectivity of the first linear-map pullback projection"]
theorem fst_surjective (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (hg : Function.Surjective g) : Function.Surjective (fst f g) := by
  intro m
  obtain ⟨n, hn⟩ := hg (f m)
  exact ⟨⟨(m, n), hn.symm⟩, rfl⟩

/-- The second projection is surjective when the first defining map is surjective. -/
@[stacks 0H7M "surjectivity of the second linear-map pullback projection"]
theorem snd_surjective (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (hf : Function.Surjective f) : Function.Surjective (snd f g) := by
  intro n
  obtain ⟨m, hm⟩ := hf (g n)
  exact ⟨⟨(m, n), hm⟩, rfl⟩

end Pullback

end LinearMap
