/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.LinearMap.Factorisation.Projective
public import ReasLib.RingTheory.Finiteness.Projective

@[expose] public section

/-!
# Linear maps factoring through finite projective modules

@stack 0G91
-/

universe u v w

namespace LinearMap

section Semiring

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

namespace Factorisation

/-- A linear-map factorisation with a finite projective midpoint. -/
@[stacks 0G91 "structured finite-projective factorisation"]
structure FiniteProjective (f : M →ₗ[R] N) where
  /-- The underlying factorisation. -/
  base : Factorisation f
  /-- Finite projectivity of the selected midpoint. -/
  property : Module.FiniteProjective R base.mid

namespace FiniteProjective

variable {f : M →ₗ[R] N}

/-- Build a finite-projective factorisation from a finite-projective midpoint and two maps. -/
@[stacks 0G91 "constructor for finite-projective factorisations"]
def ofMaps (P : Type (max u v w)) [AddCommMonoid P] [Module R P]
    (property : Module.FiniteProjective R P) (fromSource : M →ₗ[R] P)
    (toTarget : P →ₗ[R] N) (factor : toTarget.comp fromSource = f) :
    FiniteProjective f where
  base :=
    { mid := SemimoduleCat.of R P
      fromSource := fromSource
      toTarget := toTarget
      factor := factor }
  property := property

/-- The midpoint of a finite-projective factorisation. -/
@[stacks 0G91 "midpoint of a finite-projective factorisation"]
abbrev mid (F : FiniteProjective f) := F.base.mid

/-- The midpoint of a finite-projective factorisation is finite. -/
@[stacks 0G91 "finiteness of the factorisation midpoint"]
abbrev finite (F : FiniteProjective f) : Module.Finite R F.mid := F.property.finite

/-- The midpoint of a finite-projective factorisation is projective. -/
@[stacks 0G91 "projectivity of the factorisation midpoint"]
abbrev projective (F : FiniteProjective f) : Module.Projective R F.mid := F.property.projective

/-- The source map of a finite-projective factorisation. -/
@[stacks 0G91 "source map of a finite-projective factorisation"]
abbrev fromSource (F : FiniteProjective f) : M →ₗ[R] F.mid := F.base.fromSource

/-- The target map of a finite-projective factorisation. -/
@[stacks 0G91 "target map of a finite-projective factorisation"]
abbrev toTarget (F : FiniteProjective f) : F.mid →ₗ[R] N := F.base.toTarget

/-- The triangle equation of a finite-projective factorisation. -/
theorem factor (F : FiniteProjective f) : F.toTarget.comp F.fromSource = f := by
  exact F.base.factor

/-- Forget finiteness from a finite-projective factorisation. -/
@[stacks 0G91 "finite-projective factorisation as projective"]
def toProjective (F : FiniteProjective f) : Factorisation.Projective f where
  base := F.base
  projective := F.property.projective

end FiniteProjective

end Factorisation

/-- A linear map factors through a finite projective module. -/
@[stacks 0G91 "factorisation through a finite projective module"]
abbrev FactorsThroughFiniteProjective (f : M →ₗ[R] N) : Prop :=
  Nonempty (Factorisation.FiniteProjective f)

/-- The zero map factors through a finite projective module. -/
theorem factorsThroughFiniteProjective_zero :
    FactorsThroughFiniteProjective (0 : M →ₗ[R] N) := by
  refine ⟨Factorisation.FiniteProjective.ofMaps (ULift.{max v w} R)
    ⟨inferInstance, inferInstance⟩ 0 0 ?_⟩
  simp

/-- Finite-projective-factor maps are closed under addition. -/
theorem FactorsThroughFiniteProjective.add {f g : M →ₗ[R] N}
    (hf : f.FactorsThroughFiniteProjective) (hg : g.FactorsThroughFiniteProjective) :
    (f + g).FactorsThroughFiniteProjective := by
  rcases hf with ⟨F⟩
  rcases hg with ⟨G⟩
  letI : Module.Finite R F.mid := F.finite
  letI : Module.Finite R G.mid := G.finite
  letI : Module.Projective R F.mid := F.projective
  letI : Module.Projective R G.mid := G.projective
  refine ⟨Factorisation.FiniteProjective.ofMaps (F.mid × G.mid)
    ⟨inferInstance, inferInstance⟩ (F.fromSource.prod G.fromSource)
    (F.toTarget.coprod G.toTarget) ?_⟩
  ext x
  change F.toTarget (F.fromSource x) + G.toTarget (G.fromSource x) = f x + g x
  rw [← LinearMap.comp_apply, F.factor, ← LinearMap.comp_apply, G.factor]

/-- A finite-projective factorisation is a projective factorisation. -/
theorem FactorsThroughFiniteProjective.projective {f : M →ₗ[R] N}
    (hf : f.FactorsThroughFiniteProjective) : f.FactorsThroughProjective := by
  rcases hf with ⟨F⟩
  exact ⟨F.toProjective⟩

/-- For a finite source, a projective factorisation can be chosen finite projective. -/
@[stacks 0G91]
theorem FactorsThroughProjective.finite [Module.Finite R M] {f : M →ₗ[R] N}
    (hf : f.FactorsThroughProjective) : f.FactorsThroughFiniteProjective := by
  classical
  rcases hf with ⟨F⟩
  obtain ⟨split, hsplit⟩ := F.projective.out
  obtain ⟨n, gen, hgen⟩ := (Module.Finite.exists_fin (R := R) (M := M))
  let S : Finset F.mid := Finset.univ.biUnion
    (fun j : Fin n => (split (F.fromSource (gen j))).support)
  let ι := {p : F.mid // p ∈ S}
  let incl : ι → F.mid := fun p => p.1
  have incl_inj : Function.Injective incl := Subtype.val_injective
  let lift : (ι →₀ R) →ₗ[R] (F.mid →₀ R) :=
    Finsupp.lmapDomain R R incl
  let restrict : (F.mid →₀ R) →ₗ[R] (ι →₀ R) :=
    Finsupp.lcomapDomain incl incl_inj
  let comb : (F.mid →₀ R) →ₗ[R] F.mid :=
    Finsupp.linearCombination R (fun x : F.mid => x)
  have hsupport (j : Fin n) :
      (↑(split (F.fromSource (gen j))).support : Set F.mid) ⊆ Set.range incl := by
    intro p hp
    refine ⟨⟨p, ?_⟩, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hp⟩
  have hfactor :
      ((F.toTarget.comp comb).comp lift).comp
          (restrict.comp (split.comp F.fromSource)) = f := by
    apply LinearMap.ext_on_range hgen
    intro j
    change F.toTarget (comb
      (Finsupp.mapDomain incl (Finsupp.comapDomain incl
        (split (F.fromSource (gen j))) incl_inj.injOn))) = f (gen j)
    rw [Finsupp.mapDomain_comapDomain incl incl_inj
      (split (F.fromSource (gen j))) (hsupport j)]
    have hcomb : comb (split (F.fromSource (gen j))) = F.fromSource (gen j) := by
      rw [show comb = Finsupp.linearCombination R (_root_.id : F.mid → F.mid) by
        dsimp [comb]
        congr 1]
      exact hsplit (F.fromSource (gen j))
    rw [hcomb]
    rw [← LinearMap.comp_apply, F.base.factor]
  refine ⟨Factorisation.FiniteProjective.ofMaps (ι →₀ R)
    ⟨inferInstance, inferInstance⟩ (restrict.comp (split.comp F.fromSource))
    ((F.toTarget.comp comb).comp lift) hfactor⟩

end Semiring

section CommSemiring

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- Finite-projective-factor maps are closed under scalar multiplication. -/
theorem FactorsThroughFiniteProjective.smul (r : R) {f : M →ₗ[R] N}
    (hf : f.FactorsThroughFiniteProjective) :
    (r • f).FactorsThroughFiniteProjective := by
  rcases hf with ⟨F⟩
  refine ⟨Factorisation.FiniteProjective.ofMaps F.mid F.property F.fromSource
    (r • F.toTarget) ?_⟩
  ext x
  change r • F.toTarget (F.fromSource x) = r • f x
  rw [← LinearMap.comp_apply, F.factor]

/-- The submodule of maps which factor through a finite projective module. -/
@[stacks 0G91 "finite-projective-factor submodule"]
def finiteProjectiveFactors : Submodule R (M →ₗ[R] N) where
  carrier := FactorsThroughFiniteProjective
  zero_mem' := factorsThroughFiniteProjective_zero
  add_mem' := FactorsThroughFiniteProjective.add
  smul_mem' := FactorsThroughFiniteProjective.smul

/-- Membership in `finiteProjectiveFactors` is finite-projective factorisation. -/
theorem mem_finiteProjectiveFactors (f : M →ₗ[R] N) :
    f ∈ finiteProjectiveFactors (R := R) (M := M) (N := N) ↔
      f.FactorsThroughFiniteProjective := by
  rfl

/-- For a finite source, projective-factor and finite-projective-factor submodules agree. -/
@[stacks 0G91 "submodule form"]
theorem projectiveFactors_eq_finiteProjectiveFactors [Module.Finite R M] :
    projectiveFactors (R := R) (M := M) (N := N) =
      finiteProjectiveFactors (R := R) (M := M) (N := N) := by
  ext f
  change f.FactorsThroughProjective ↔ f.FactorsThroughFiniteProjective
  constructor
  · exact FactorsThroughProjective.finite
  · exact FactorsThroughFiniteProjective.projective

end CommSemiring

end LinearMap
