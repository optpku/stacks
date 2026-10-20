/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

@[expose] public section

/-!
# Cokernels of Cochain Differentials

This leaf records the cokernel of the incoming differential in a cochain
complex and its functoriality under cochain maps.  It is independent of the
module category in which a later application is carried out.
@stack 0653
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The cokernel of the incoming differential into degree `n` of a cochain complex. -/
@[stacks 0653 "incoming differential cokernel"]
abbrev differentialCokernel (K : CochainComplex C ℤ) (n : ℤ) : C :=
  cokernel (K.d (n - 1) n)

/-- The map on incoming-differential cokernels induced by a cochain map. -/
@[stacks 0653 "map on incoming differential cokernels"]
abbrev differentialCokernelMap {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    differentialCokernel K n ⟶ differentialCokernel L n :=
  cokernel.map (K.d (n - 1) n) (L.d (n - 1) n) (f.f (n - 1)) (f.f n)
    (f.comm (n - 1) n).symm

/-- The quotient map into an incoming-differential cokernel commutes with the map induced by a
cochain map. -/
@[reassoc, stacks 0653 "naturality of incoming differential cokernels"]
theorem π_differentialCokernelMap {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    cokernel.π (K.d (n - 1) n) ≫ differentialCokernelMap f n =
      f.f n ≫ cokernel.π (L.d (n - 1) n) := sorry

/-- A cochain map is monic on differential cokernels when the induced map is monic in every
degree. -/
@[stacks 0653 "monicity on incoming differential cokernels"]
def MonoOnDifferentialCokernels {K L : CochainComplex C ℤ} (f : K ⟶ L) : Prop :=
  ∀ n : ℤ, Mono (differentialCokernelMap f n)

namespace MonoOnDifferentialCokernels

/-- A cochain map which is monic on differential cokernels has a monic induced cokernel map in
each specified degree. -/
@[stacks 0653 "degreewise monicity on incoming differential cokernels"]
theorem mono {K L : CochainComplex C ℤ} {f : K ⟶ L}
    (hf : MonoOnDifferentialCokernels f) (n : ℤ) :
    Mono (differentialCokernelMap f n) := sorry

end MonoOnDifferentialCokernels

end CochainComplex
