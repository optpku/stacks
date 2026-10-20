/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.CokernelAcyclic
public import ReasLib.Algebra.Homology.HomologicalComplex.KernelAcyclic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Termwise mono and epi quasi-isomorphisms of cochain complexes

The root owners for acyclic kernels and cokernels are formulated for arbitrary homological
complexes.  This leaf gives the cochain-complex specializations used by lifting arguments and
records the boundary-subobject computation for a termwise monomorphic quasi-isomorphism.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The cokernel complex of a termwise monomorphic quasi-isomorphism is acyclic. -/
@[stacks 013Q]
theorem acyclic_cokernel_of_quasiIso_of_termwiseMono
    {K L : CochainComplex A ℤ} (f : K ⟶ L) [QuasiIso f]
    (hmono : ∀ n : ℤ, Mono (f.f n)) :
    (cokernel f).Acyclic := sorry

/-- The kernel complex of a termwise epimorphic quasi-isomorphism is acyclic. -/
@[stacks 0649]
theorem acyclic_kernel_of_quasiIso_of_termwiseEpi
    {K L : CochainComplex A ℤ} (f : K ⟶ L) [QuasiIso f]
    (hepi : ∀ n : ℤ, Epi (f.f n)) :
    (kernel f).Acyclic := sorry

/-- For a termwise monomorphic quasi-isomorphism, the image of the incoming differential in
the source, mapped to the target, is the intersection of the comparison image with the target
boundary subobject. -/
@[stacks 013Q]
theorem image_dTo_comp_eq_inf_of_quasiIso_of_termwiseMono
    {K L : CochainComplex A ℤ} (f : K ⟶ L) [QuasiIso f]
    (hmono : ∀ n : ℤ, Mono (f.f n)) (n : ℤ) :
    imageSubobject (K.dTo n ≫ f.f n) =
      imageSubobject (f.f n) ⊓ imageSubobject (L.dTo n) := sorry

end CochainComplex
