/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Tensor

/-!
# Flatness consequences of universal exactness

This module separates the flatness consequences of a universally exact short complex from the
definition of universal exactness itself.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open CategoryTheory.ShortComplex

universe u v

namespace CategoryTheory.ShortComplex

variable {R : Type u} [CommRing R]

namespace LinearMap.UniversallyInjective

variable {M N : Type v}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The domain of a universally injective map into a flat module is flat. -/
theorem flat_domain {f : M →ₗ[R] N}
    (hf : LinearMap.UniversallyInjective.{u, v, v, max u v} f)
    [Module.Flat R N] :
    Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro A B _ _ _ _ g hg x y hxy
  apply hf.rTensor_injective A
  apply Module.Flat.lTensor_preserves_injective_linearMap g hg
  calc
    g.lTensor N (f.rTensor A x) = TensorProduct.map f g x := by
      change ((g.lTensor N).comp (f.rTensor A)) x = _
      rw [LinearMap.lTensor_comp_rTensor]
    _ = f.rTensor B (g.lTensor M x) := by
      change _ = ((f.rTensor B).comp (g.lTensor M)) x
      rw [LinearMap.rTensor_comp_lTensor]
    _ = f.rTensor B (g.lTensor M y) := congrArg _ hxy
    _ = TensorProduct.map f g y := by
      change ((f.rTensor B).comp (g.lTensor M)) y = _
      rw [LinearMap.rTensor_comp_lTensor]
    _ = g.lTensor N (f.rTensor A y) := by
      change _ = ((g.lTensor N).comp (f.rTensor A)) y
      rw [LinearMap.lTensor_comp_rTensor]

variable {P : Type v} [AddCommGroup P] [Module R P]

/-- The cokernel term of an exact pair is flat when the first map is universally injective and
the middle term is flat. -/
theorem flat_cokernel {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hf : LinearMap.UniversallyInjective.{u, v, v, max u v} f)
    (hexact : Function.Exact f g)
    (hg : Function.Surjective g) [Module.Flat R N] :
    Module.Flat R P := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
    hexact hg (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective I)
    (hf.rTensor_injective (R ⧸ I))
    (Module.Flat.lTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)

end LinearMap.UniversallyInjective

namespace ShortExact

/-- A short exact complex of modules with flat right term is universally exact. -/
@[stacks 00HL]
theorem universallyExact_of_flat_X₃ {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) [Module.Flat R S.X₃] :
    S.UniversallyExact := by
  refine ⟨hS, ?_⟩
  intro Q _ _
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  exact LinearMap.lTensor_injective_of_exact_of_flat
    S.g.hom hS.moduleCat_surjective_g S.f.hom hS.moduleCat_injective_f
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact) Q

/-- In a short exact complex with flat middle and right terms, the left term is flat. -/
@[stacks 00HM "(2)"]
theorem flat_X₁ {S : ShortComplex (ModuleCat.{v} R)}
    [Module.Flat R S.X₂] [Module.Flat R S.X₃] (hS : S.ShortExact) :
    Module.Flat R S.X₁ :=
  (universallyExact_of_flat_X₃ hS).universallyInjective_f.flat_domain

/-- In a short exact complex with flat left and right terms, the middle term is flat. -/
@[stacks 00HM "(1)"]
theorem flat_X₂ {S : ShortComplex (ModuleCat.{v} R)}
    [Module.Flat R S.X₁] [Module.Flat R S.X₃] (hS : S.ShortExact) :
    Module.Flat R S.X₂ := by
  let hU : S.UniversallyExact := universallyExact_of_flat_X₃ hS
  have hExact : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro A B _ _ _ _ k hk x y hxy
  have hgxy : S.g.hom.rTensor A x = S.g.hom.rTensor A y := by
    apply Module.Flat.lTensor_preserves_injective_linearMap k hk
    calc
      k.lTensor S.X₃ (S.g.hom.rTensor A x) =
          TensorProduct.map S.g.hom k x := by
        change ((k.lTensor S.X₃).comp (S.g.hom.rTensor A)) x = _
        rw [LinearMap.lTensor_comp_rTensor]
      _ = S.g.hom.rTensor B (k.lTensor S.X₂ x) := by
        change _ = ((S.g.hom.rTensor B).comp (k.lTensor S.X₂)) x
        rw [LinearMap.rTensor_comp_lTensor]
      _ = S.g.hom.rTensor B (k.lTensor S.X₂ y) := congrArg _ hxy
      _ = TensorProduct.map S.g.hom k y := by
        change ((S.g.hom.rTensor B).comp (k.lTensor S.X₂)) y = _
        rw [LinearMap.rTensor_comp_lTensor]
      _ = k.lTensor S.X₃ (S.g.hom.rTensor A y) := by
        change _ = ((k.lTensor S.X₃).comp (S.g.hom.rTensor A)) y
        rw [LinearMap.lTensor_comp_rTensor]
  have hTensorExact :
      Function.Exact (S.f.hom.rTensor A) (S.g.hom.rTensor A) :=
    rTensor_exact A hExact hS.moduleCat_surjective_g
  have hker : x - y ∈ LinearMap.ker (S.g.hom.rTensor A) := by
    rw [LinearMap.mem_ker, map_sub, hgxy, sub_self]
  rw [hTensorExact.linearMap_ker_eq] at hker
  obtain ⟨z, hz⟩ := hker
  have hkz : k.lTensor S.X₁ z = 0 := by
    apply hU.universallyInjective_f.rTensor_injective B
    calc
      S.f.hom.rTensor B (k.lTensor S.X₁ z) =
          TensorProduct.map S.f.hom k z := by
        change ((S.f.hom.rTensor B).comp (k.lTensor S.X₁)) z = _
        rw [LinearMap.rTensor_comp_lTensor]
      _ = k.lTensor S.X₂ (S.f.hom.rTensor A z) := by
        change _ = ((k.lTensor S.X₂).comp (S.f.hom.rTensor A)) z
        rw [LinearMap.lTensor_comp_rTensor]
      _ = k.lTensor S.X₂ (x - y) := congrArg _ hz
      _ = 0 := by rw [map_sub, hxy, sub_self]
      _ = S.f.hom.rTensor B 0 := by rw [map_zero]
  have hz0 : z = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap k hk
    simpa using hkz
  apply sub_eq_zero.mp
  rw [← hz, hz0, map_zero]

/-- Tensoring a short exact complex with flat right term on the left by any module preserves
short exactness. -/
theorem tensorLeft_shortExact_of_flat_X₃ {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) [Module.Flat R S.X₃] (N : ModuleCat.{u} R) :
    (S.map (tensorLeft N)).ShortExact :=
  (universallyExact_of_flat_X₃ hS).tensorLeft_shortExact N

end ShortExact

variable {S : ShortComplex (ModuleCat.{v} R)}

/-- Universal exactness makes every right tensor map induced by the left morphism injective. -/
theorem rTensor_f_injective_of_universallyExact
    (hS : UniversallyExact S) (Q : Type (max u v)) [AddCommGroup Q] [Module R Q] :
    Function.Injective (S.f.hom.rTensor Q) :=
  hS.universallyInjective_f.rTensor_injective Q

/-- If the middle term of a universally exact short complex is flat, then both the left and right
terms are flat. -/
@[stacks 058P]
theorem flat_X₁_and_X₃_of_universallyExact
    [Module.Flat R S.X₂] (hS : UniversallyExact S) :
    Module.Flat R S.X₁ ∧ Module.Flat R S.X₃ := by
  have h₁ : Module.Flat R S.X₁ := hS.universallyInjective_f.flat_domain
  have h₃ : Module.Flat R S.X₃ := hS.universallyInjective_f.flat_cokernel
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.shortExact.exact)
    hS.shortExact.moduleCat_surjective_g
  exact ⟨h₁, h₃⟩

namespace UniversallyExact

/-- In a universally exact short complex, flatness of the middle term implies flatness of the
left term. -/
@[stacks 058P]
theorem flat_X₁ [Module.Flat R S.X₂] (hS : UniversallyExact S) :
    Module.Flat R S.X₁ := (flat_X₁_and_X₃_of_universallyExact hS).1

/-- In a universally exact short complex, flatness of the middle term implies flatness of the
right term. -/
@[stacks 058P]
theorem flat_X₃ [Module.Flat R S.X₂] (hS : UniversallyExact S) :
    Module.Flat R S.X₃ := (flat_X₁_and_X₃_of_universallyExact hS).2

end UniversallyExact

end CategoryTheory.ShortComplex

namespace Module.Flat

open CategoryTheory

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- An `R`-module `M` is flat if and only if every short exact complex whose right term is
isomorphic to `M` is universally exact. -/
@[stacks 058M]
theorem iff_forall_shortExact_universallyExact :
    Module.Flat R M ↔
      ∀ (S : CategoryTheory.ShortComplex (ModuleCat.{v} R)),
        S.ShortExact →
        Nonempty (S.X₃ ≅ ModuleCat.of R M) →
        S.UniversallyExact := sorry

end Module.Flat
