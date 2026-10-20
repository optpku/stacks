/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective.Basic

/-!
# Functorial acyclic enlargement of DG modules

An acyclic enlargement is an endofunctor equipped with a monomorphic quasi-isomorphism from the
identity and fillers against a fixed set-indexed family of acyclic monomorphisms.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib intentionally keeps this construction non-global because a global instance breaks
-- sheaf/free elaboration.  Enlargement fillers use the same K-injective homotopy structure.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Module.KInjective

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- A functorial enlargement solving all extension problems against a chosen family of acyclic
monomorphisms. -/
@[stacks 0FSZ]
structure AcyclicEnlargement (𝒜 : DGA(𝒪)) {R : Type w}
    (source target : R → Mod(𝒜, d))
    (arrow : ∀ r, source r ⟶ target r) where
  /-- The enlargement endofunctor. -/
  functor : Mod(𝒜, d) ⥤ Mod(𝒜, d)
  /-- The comparison from each module to its enlargement. -/
  ι : 𝟭 (Mod(𝒜, d)) ⟶ functor
  /-- The comparison is a monomorphism of natural transformations. -/
  mono_ι : Mono ι
  /-- Every comparison component is a quasi-isomorphism. -/
  quasiIso_ι_app (M : Mod(𝒜, d)) : Module.quasiIso 𝒜 (ι.app M)
  /-- Every extension problem against a chosen arrow admits a filler after enlargement. -/
  has_filler {r : R} {M : Mod(𝒜, d)} (f : source r ⟶ M) :
    ∃ g : target r ⟶ functor.obj M, CommSq (arrow r) f g (ι.app M)

namespace AcyclicEnlargement

/-- Every component of an acyclic-enlargement comparison is a monomorphism. -/
theorem mono_app {𝒜 : DGA(𝒪)} {R : Type w}
    {source target : R → Mod(𝒜, d)} {arrow : ∀ r, source r ⟶ target r}
    (E : AcyclicEnlargement 𝒜 source target arrow) (M : Mod(𝒜, d)) :
    Mono (E.ι.app M) := sorry

/-- Every set-indexed family of monomorphisms between acyclic DG modules admits a functorial
acyclic enlargement. -/
@[stacks 0FSZ "existence"]
theorem nonempty (𝒜 : DGA(𝒪)) {R : Type w}
    (source target : R → Mod(𝒜, d))
    (arrow : ∀ r, source r ⟶ target r)
    (h_arrow : ∀ r, Mono (arrow r))
    (h_source : ∀ r, Module.acyclic 𝒜 (source r))
    (h_target : ∀ r, Module.acyclic 𝒜 (target r)) :
    Nonempty (AcyclicEnlargement 𝒜 source target arrow) := sorry

end AcyclicEnlargement

end


end SheafOfModules.RingedSite.DifferentialGradedModule.Module.KInjective
