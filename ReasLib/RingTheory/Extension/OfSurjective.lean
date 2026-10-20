/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Extension.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extensions Constructed from Surjective Algebra Homomorphisms

These projection lemmas expose the map and kernel packaged by
`Algebra.Extension.ofSurjective`, so consumers need not unfold the extension
structure or its generated algebra instance.

@stack 04EC
-/

@[expose] public section

noncomputable section

open Algebra

namespace Algebra.Extension

universe u v w

/-- The structure map of an extension built from a surjective algebra
homomorphism is the original homomorphism. -/
@[simp, stacks 04EC "surjective extension structure map"]
theorem toAlgHom_ofSurjective
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    (f : A →ₐ[R] S) (hf : Function.Surjective f) :
    IsScalarTower.toAlgHom R (Extension.ofSurjective f hf).Ring S = f :=
  rfl

/-- The kernel packaged by `Extension.ofSurjective` is the kernel of the
original homomorphism. -/
@[simp, stacks 04EC "surjective extension kernel"]
theorem ker_ofSurjective
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    (f : A →ₐ[R] S) (hf : Function.Surjective f) :
    (Extension.ofSurjective f hf).ker = RingHom.ker f.toRingHom :=
  rfl

end Algebra.Extension
