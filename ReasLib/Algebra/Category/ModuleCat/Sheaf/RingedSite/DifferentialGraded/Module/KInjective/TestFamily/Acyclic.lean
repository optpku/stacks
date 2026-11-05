/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Acyclic

/-!
# Set-sized test families of acyclic differential graded modules

An acyclic test family consists of nonzero acyclic DG modules and is cofinal for
monomorphisms into nonzero acyclic DG modules. It is
packaged as explicit data so later small-object and K-injective constructions can carry a
single reusable value.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Module.KInjective

section


variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- A set-indexed family detecting nonzero acyclic DG modules by monomorphisms from its
nonzero members. The nonzero condition ensures strict growth in acyclic filtrations. -/
@[stacks 0FST]
structure AcyclicTestFamily (𝒜 : DGA(𝒪)) where
  /-- The set-sized index type. -/
  index : Type w
  /-- The DG module assigned to an index. -/
  obj : index → Mod(𝒜, d)
  /-- Every family member has acyclic underlying cochain complex. -/
  obj_acyclic (r : index) : Module.acyclic 𝒜 (obj r)
  /-- Every family member is nonzero. -/
  nonzero_obj (r : index) : ¬ IsZero (obj r)
  /-- Every nonzero acyclic DG module receives a monomorphism from a family member. -/
  exists_mono {M : Mod(𝒜, d)} (hM : Module.acyclic 𝒜 M)
      (hM_zero : ¬ IsZero M) :
      ∃ r : index, ∃ f : obj r ⟶ M, Mono f

namespace AcyclicTestFamily

/-- A nonzero acyclic test family, indexed in the coefficient universe, exists for every
sheaf of differential graded algebras. -/
@[stacks 0FST "existence"]
theorem nonempty (𝒜 : DGA(𝒪)) :
    Nonempty (AcyclicTestFamily.{u, v, max u v} 𝒜) := sorry

end AcyclicTestFamily

end


end SheafOfModules.RingedSite.DifferentialGradedModule.Module.KInjective
