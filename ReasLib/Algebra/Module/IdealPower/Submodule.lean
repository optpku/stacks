/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Submodules in the ideal-power filtration

This file owns the module-level `I`-adic submodule construction.  It is deliberately
independent of the quotient-stage and homology files: a filtered module, its restricted
maps, and the corresponding `ModuleCat` functor form reusable ideal-power filtration API.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w uι

namespace Ideal.PowerSubmodule

section Unbundled

variable {A : Type u} [CommSemiring A]

/-- The `n`th submodule in the `I`-adic filtration of an `A`-module. -/
@[stacks 0G3K "adic submodule stage"]
abbrev stage (I : Ideal A) (M : Type v) [AddCommMonoid M] [Module A M] (n : ℕ) :
    Submodule A M :=
  I ^ n • (⊤ : Submodule A M)

/-- The inclusion of an adic stage into its ambient module. -/
@[stacks 0G3K "adic stage inclusion"]
abbrev subtype (I : Ideal A) (M : Type v) [AddCommMonoid M] [Module A M] (n : ℕ) :
    stage I M n →ₗ[A] M :=
  (stage I M n).subtype

/-- The adic filtration is antitone in the exponent. -/
@[stacks 0G3K "adic stage monotonicity"]
theorem stage_antitone (I : Ideal A) {M : Type v} [AddCommMonoid M] [Module A M]
    {m n : ℕ} (h : m ≤ n) : stage I M n ≤ stage I M m := by
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

/-- On the regular module, the `n`th adic stage is the ideal `I ^ n` itself. -/
@[stacks 0G3K "adic stage of the regular module"]
theorem stage_regular (I : Ideal A) (n : ℕ) : stage I A n = I ^ n := by
  exact Ideal.mul_top (I ^ n)

/-- A linear map restricts canonically to every adic stage. -/
@[stacks 0G3K "adic stage map denominator bound"]
theorem map_le (I : Ideal A) {M : Type v} {N : Type w} [AddCommMonoid M] [Module A M]
    [AddCommMonoid N] [Module A N] (f : M →ₗ[A] N) (n : ℕ) :
    Submodule.map f (stage I M n) ≤ stage I N n := by
  change (I ^ n • (⊤ : Submodule A M)).map f ≤ I ^ n • (⊤ : Submodule A N)
  rw [Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top

/-- A representative of an adic stage remains in the same stage after applying a map. -/
@[stacks 0G3K "adic stage map membership"]
theorem map_mem (I : Ideal A) {M : Type v} {N : Type w} [AddCommMonoid M] [Module A M]
    [AddCommMonoid N] [Module A N] (f : M →ₗ[A] N) (n : ℕ)
    {x : M} (hx : x ∈ stage I M n) : f x ∈ stage I N n := by
  exact map_le I f n (Submodule.mem_map_of_mem hx)

/-- The restriction of a linear map to the corresponding adic stages. -/
@[stacks 0G3K "adic stage map"]
noncomputable abbrev map (I : Ideal A) {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module A M]
    [AddCommMonoid N] [Module A N] (f : M →ₗ[A] N) (n : ℕ) :
    stage I M n →ₗ[A] stage I N n :=
  f.restrict (fun _ hx ↦ map_mem I f n hx)

/-- Injective maps remain injective on every adic stage. -/
@[stacks 0G3K "injective adic stage map"]
theorem map_injective
    (I : Ideal A) {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N]
    (f : M →ₗ[A] N) (hf : Function.Injective f) (n : ℕ) :
    Function.Injective (map I f n) := by
  intro x y hxy
  apply Subtype.ext
  exact hf (congrArg Subtype.val hxy)

/-- Surjections remain surjective on every adic stage. -/
@[stacks 0G3K "surjective adic stage map"]
theorem map_surjective
    (I : Ideal A) {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N]
    (f : M →ₗ[A] N) (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (map I f n) := by
  have hmap : (stage I M n).map f = stage I N n := by
    change (I ^ n • (⊤ : Submodule A M)).map f = I ^ n • (⊤ : Submodule A N)
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]
  intro y
  have hy : (y : N) ∈ (stage I M n).map f := by
    rw [hmap]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- Evaluation of a restricted adic-stage map. -/
@[simp, stacks 0G3K "adic stage map evaluation"]
theorem map_apply (I : Ideal A) {M : Type v} {N : Type w} [AddCommMonoid M] [Module A M]
    [AddCommMonoid N] [Module A N] (f : M →ₗ[A] N) (n : ℕ)
    (x : stage I M n) : (map I f n x : N) = f x := by
  rfl

/-- The restricted map agrees with the ambient map after the stage inclusions. -/
@[stacks 0G3K "adic stage map inclusion formula"]
theorem map_comp_subtype (I : Ideal A) {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N]
    (f : M →ₗ[A] N) (n : ℕ) :
    (subtype I N n).comp (map I f n) = f.comp (subtype I M n) := by
  rfl

/-- A linear map from a deeper source stage to any shallower target stage. -/
@[stacks 0G3L "linear map between unequal adic stages"]
noncomputable abbrev mapToStage
    (I : Ideal A) {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N]
    (f : M →ₗ[A] N) {m n : ℕ} (h : m ≤ n) :
    stage I M n →ₗ[A] stage I N m :=
  (Submodule.inclusion (stage_antitone I h)).comp (map I f n)

/-- An unequal-stage map evaluates as the original ambient linear map. -/
@[simp, stacks 0G3L "unequal adic-stage map evaluation"]
theorem mapToStage_apply
    (I : Ideal A) {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N]
    (f : M →ₗ[A] N) {m n : ℕ} (h : m ≤ n) (x : stage I M n) :
    ((mapToStage I f h x : stage I N m) : N) = f x := by
  rfl

/-- Forgetting an unequal target stage recovers restriction along the source-stage inclusion. -/
@[stacks 0G3L "unequal adic-stage map inclusion formula"]
theorem subtype_comp_mapToStage
    (I : Ideal A) {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N]
    (f : M →ₗ[A] N) {m n : ℕ} (h : m ≤ n) :
    (subtype I N m).comp (mapToStage I f h) = f.comp (subtype I M n) := by
  rfl

/-- Unequal-stage restriction preserves addition of ambient linear maps. -/
@[stacks 0G3L "unequal adic-stage restriction preserves addition"]
theorem mapToStage_add
    (I : Ideal A) {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N]
    (f g : M →ₗ[A] N) {m n : ℕ} (h : m ≤ n) :
    mapToStage I (f + g) h = mapToStage I f h + mapToStage I g h := by
  ext x
  rfl

/-- Unequal-stage restriction commutes with scalar multiplication of ambient linear maps. -/
@[stacks 0G3L "unequal adic-stage restriction preserves scalar multiplication"]
theorem mapToStage_smul
    (I : Ideal A) {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N]
    (a : A) (f : M →ₗ[A] N) {m n : ℕ} (h : m ≤ n) :
    mapToStage I (a • f) h = a • mapToStage I f h := by
  ext x
  rfl

/-- Restriction to unequal adic stages is linear in the ambient map. -/
@[stacks 0G3L "linear family of unequal adic-stage maps"]
noncomputable def mapToStageLinear
    (I : Ideal A) (M : Type v) (N : Type w)
    [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N]
    {m n : ℕ} (h : m ≤ n) :
    (M →ₗ[A] N) →ₗ[A] (stage I M n →ₗ[A] stage I N m) where
  toFun f := mapToStage I f h
  map_add' f g := mapToStage_add I f g h
  map_smul' a f := mapToStage_smul I a f h

/-- A pointwise family in an adic stage is an adic-stage element of a finite product. -/
@[stacks 0G3K "adic stage finite-product membership"]
theorem pi_mem (I : Ideal A) {ι : Type uι} {M : Type v} [Finite ι]
    [AddCommMonoid M] [Module A M] (n : ℕ) (x : ι → M)
    (hx : ∀ i, x i ∈ stage I M n) : x ∈ stage I (ι → M) n := by
  classical
  -- Local instance justification (proof-local temporary data): enumerate the finite coordinates for LinearMap.sum_single_apply and the adic-stage finite sum.
  letI := Fintype.ofFinite ι
  rw [← LinearMap.sum_single_apply (fun _ : ι ↦ M) x]
  exact (stage I (ι → M) n).sum_mem fun i _ ↦
    map_mem I (LinearMap.single A (fun _ : ι ↦ M) i) n (hx i)

end Unbundled

section Bundled

variable {A : Type u} [CommRing A]

/-- The adic stage as an object of `ModuleCat A`. -/
@[stacks 0G3K "bundled adic stage"]
abbrev stageObj (I : Ideal A) (M : ModuleCat.{v} A) (n : ℕ) : ModuleCat.{v} A :=
  ModuleCat.of A (stage I M n)

/-- The bundled adic stage of the regular module is the corresponding ideal as a module. -/
@[stacks 0G3K "bundled adic stage of the regular module"]
theorem stageObj_regular (I : Ideal A) (n : ℕ) :
    stageObj I (ModuleCat.of A A) n = ModuleCat.of A ↥(I ^ n) := by
  exact congrArg (fun P : Submodule A A ↦ ModuleCat.of A P) (stage_regular I n)

/-- The adic stage map as a morphism of `ModuleCat A`. -/
@[stacks 0G3K "bundled adic stage map"]
noncomputable def mapObj (I : Ideal A) {M N : ModuleCat.{v} A}
    (f : M ⟶ N) (n : ℕ) : stageObj I M n ⟶ stageObj I N n :=
  ModuleCat.ofHom (map I f.hom n)

/-- Restricting a monomorphism to an adic stage remains a monomorphism. -/
@[stacks 0G3K "adic stage map preserves monomorphisms"]
instance mapObj_mono
    (I : Ideal A) {M N : ModuleCat.{v} A} (f : M ⟶ N) [Mono f] (n : ℕ) :
    Mono (mapObj I f n) := by
  apply (ModuleCat.mono_iff_injective _).mpr
  exact map_injective I f.hom ((ModuleCat.mono_iff_injective f).mp inferInstance) n

/-- Restricting an epimorphism to an adic stage remains an epimorphism. -/
@[stacks 0G3K "adic stage map preserves epimorphisms"]
instance mapObj_epi
    (I : Ideal A) {M N : ModuleCat.{v} A} (f : M ⟶ N) [Epi f] (n : ℕ) :
    Epi (mapObj I f n) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  exact map_surjective I f.hom ((ModuleCat.epi_iff_surjective f).mp inferInstance) n

/-- Evaluation of the bundled adic-stage map after the ambient inclusion. -/
@[simp, stacks 0G3K "bundled adic stage map inclusion formula"]
theorem mapObj_comp_subtype (I : Ideal A) {M N : ModuleCat.{v} A}
    (f : M ⟶ N) (n : ℕ) :
    mapObj I f n ≫ ModuleCat.ofHom (subtype I N n) =
      ModuleCat.ofHom (subtype I M n) ≫ f := by
  ext x
  rfl

/-- Restriction to an adic stage sends identity morphisms to identities. -/
@[simp, stacks 0G3K "bundled adic stage map identity"]
theorem mapObj_id (I : Ideal A) (M : ModuleCat.{v} A) (n : ℕ) :
    mapObj I (𝟙 M) n = 𝟙 _ := by
  ext x
  rfl

/-- Restriction to an adic stage preserves composition. -/
@[stacks 0G3K "bundled adic stage map composition"]
theorem mapObj_comp (I : Ideal A) {M N P : ModuleCat.{v} A}
    (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) :
    mapObj I (f ≫ g) n = mapObj I f n ≫ mapObj I g n := by
  ext x
  rfl

/-- The functor taking a module to its `n`th adic stage. -/
@[stacks 0G3K "adic stage functor"]
noncomputable def functor (I : Ideal A) (n : ℕ) :
    ModuleCat.{v} A ⥤ ModuleCat.{v} A where
  obj M := stageObj I M n
  map f := mapObj I f n
  map_id M := mapObj_id I M n
  map_comp f g := mapObj_comp I f g n

/-- The adic-stage functor preserves monomorphisms. -/
@[stacks 0G3K "adic stage functor preserves monomorphisms"]
instance functor_preservesMonomorphisms (I : Ideal A) (n : ℕ) :
    (functor (A := A) I n).PreservesMonomorphisms := by
  constructor
  intro M N f hf
  exact mapObj_mono I f n

/-- The adic-stage functor preserves epimorphisms. -/
@[stacks 0G3K "adic stage functor preserves epimorphisms"]
instance functor_preservesEpimorphisms (I : Ideal A) (n : ℕ) :
    (functor (A := A) I n).PreservesEpimorphisms := by
  constructor
  intro M N f hf
  exact mapObj_epi I f n

/-- The adic stage functor preserves zero morphisms. -/
@[simp, stacks 0G3K "adic stage functor zero morphisms"]
theorem functor_map_zero (I : Ideal A) (n : ℕ) (M N : ModuleCat.{v} A) :
    (functor I n).map (0 : M ⟶ N) = 0 := by
  ext x
  rfl

/-- The canonical zero-morphism structure on the adic stage functor. -/
@[stacks 0G3K "adic stage functor preserves zero morphisms"]
noncomputable instance functor_preservesZeroMorphisms (I : Ideal A) (n : ℕ) :
    (functor (A := A) I n).PreservesZeroMorphisms := by
  exact ⟨functor_map_zero I n⟩

/-- The inclusion of a deeper adic stage into a shallower one. -/
@[stacks 0G3K "adic stage transition"]
abbrev inclusion (I : Ideal A) (M : ModuleCat.{v} A) {m n : ℕ} (h : m ≤ n) :
    stageObj I M n ⟶ stageObj I M m :=
  ModuleCat.ofHom (Submodule.inclusion (stage_antitone I h))

/-- A stage transition followed by the shallower inclusion is the deeper inclusion. -/
@[simp, stacks 0G3K "adic stage transition inclusion formula"]
theorem inclusion_comp_subtype
    (I : Ideal A) (M : ModuleCat.{v} A) {m n : ℕ} (h : m ≤ n) :
    inclusion I M h ≫ ModuleCat.ofHom (subtype I M m) =
      ModuleCat.ofHom (subtype I M n) := by
  rfl

/-- A bundled module morphism from a deeper source stage to a shallower target stage. -/
@[stacks 0G3L "bundled map between unequal adic stages"]
noncomputable def mapObjToStage
    (I : Ideal A) {M N : ModuleCat.{v} A} (f : M ⟶ N)
    {m n : ℕ} (h : m ≤ n) : stageObj I M n ⟶ stageObj I N m :=
  ModuleCat.ofHom (mapToStage I f.hom h)

/-- The bundled unequal-stage map recovers the ambient morphism after inclusion. -/
@[stacks 0G3L "bundled unequal adic-stage map inclusion formula"]
theorem mapObjToStage_comp_subtype
    (I : Ideal A) {M N : ModuleCat.{v} A} (f : M ⟶ N)
    {m n : ℕ} (h : m ≤ n) :
    mapObjToStage I f h ≫ ModuleCat.ofHom (subtype I N m) =
      ModuleCat.ofHom (subtype I M n) ≫ f := by
  ext x
  rfl

/-- Bundled unequal-stage restriction preserves addition of morphisms. -/
@[stacks 0G3L "bundled unequal adic-stage restriction preserves addition"]
theorem mapObjToStage_add
    (I : Ideal A) {M N : ModuleCat.{v} A} (f g : M ⟶ N)
    {m n : ℕ} (h : m ≤ n) :
    mapObjToStage I (f + g) h = mapObjToStage I f h + mapObjToStage I g h := by
  ext x
  rfl

/-- Bundled unequal-stage restriction commutes with scalar multiplication of morphisms. -/
@[stacks 0G3L "bundled unequal adic-stage restriction preserves scalar multiplication"]
theorem mapObjToStage_smul
    (I : Ideal A) {M N : ModuleCat.{v} A} (a : A) (f : M ⟶ N)
    {m n : ℕ} (h : m ≤ n) :
    mapObjToStage I (a • f) h = a • mapObjToStage I f h := by
  ext x
  rfl

/-- Unequal-stage restriction is an `A`-linear map between bundled Hom modules. -/
@[stacks 0G3L "linear family of bundled unequal adic-stage maps"]
noncomputable def mapObjToStageLinear
    (I : Ideal A) (M N : ModuleCat.{v} A) {m n : ℕ} (h : m ≤ n) :
    (M ⟶ N) →ₗ[A] (stageObj I M n ⟶ stageObj I N m) where
  toFun f := mapObjToStage I f h
  map_add' f g := mapObjToStage_add I f g h
  map_smul' a f := mapObjToStage_smul I a f h

/-- The inclusion from an adic stage to the ambient module, naturally in the module. -/
@[stacks 0G3K "adic stage inclusion natural transformation"]
noncomputable def subtypeNatTrans (I : Ideal A) (n : ℕ) :
    functor I n ⟶ 𝟭 (ModuleCat.{v} A) where
  app M := ModuleCat.ofHom (subtype I M n)
  naturality _ _ f := mapObj_comp_subtype I f n

/-- Adic-stage transitions commute with restricted module morphisms. -/
@[stacks 0G3K "adic stage transition naturality"]
theorem mapObj_comp_inclusion
    (I : Ideal A) {M N : ModuleCat.{v} A} (f : M ⟶ N)
    {m n : ℕ} (h : m ≤ n) :
    mapObj I f n ≫ inclusion I N h = inclusion I M h ≫ mapObj I f m := by
  ext x
  rfl

/-- The transition between adic-stage functors is natural in the module. -/
@[stacks 0G3K "adic stage transition natural transformation"]
noncomputable def inclusionNatTrans (I : Ideal A) {m n : ℕ} (h : m ≤ n) :
    functor I n ⟶ functor I m where
  app M := inclusion I M h
  naturality _ _ f := mapObj_comp_inclusion I f h

end Bundled

end Ideal.PowerSubmodule
