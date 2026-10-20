/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteKernel
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherence of internal Hom

A finitely presented source makes internal Hom locally a kernel between finite copies of its
target once the canonical restriction comparisons are invertible.  The local finite-kernel
owner then gives coherence for a coherent target.  The API records only canonical comparison
maps, never arbitrary chosen restriction isomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalClosed
open SheafOfModules.RingedSite (ringedSiteModuleCategory)

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.InternalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C,
  (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Internal Hom from a finitely presented module sheaf is locally a kernel between finite
biproducts of copies of the target when the canonical restriction comparisons are invertible. -/
@[stacks 01CQ "local kernel"]
theorem finiteKernelIsLocalOfOverComparison
    (F G : ringedSiteModuleCategory J O)
    [F.IsFinitePresentation]
    [∀ U : C, (SheafOfModules.overFunctor (ringSheaf J O) U).LaxMonoidal]
    [∀ U : C, IsIso (overComparison O U F G)] :
    FiniteKernel.IsLocal G ((ihom F).obj G) := sorry

/-- If every slice restriction preserves internal Hom, the local finite-kernel conclusion follows
without exposing its individual comparison components. -/
@[stacks 01CQ "restriction preserves internal Hom"]
theorem finiteKernelIsLocalOfPreservesOver
    (F G : ringedSiteModuleCategory J O)
    [F.IsFinitePresentation]
    [∀ U : C, (SheafOfModules.overFunctor (ringSheaf J O) U).LaxMonoidal]
    [∀ U : C, CategoryTheory.Functor.LaxMonoidal.PreservesInternalHom
      (SheafOfModules.overFunctor (ringSheaf J O) U)] :
    FiniteKernel.IsLocal G ((ihom F).obj G) := sorry

section Coherent

variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ V : Over U, ∀ W : Over V,
  HasWeakSheafify (((J.over U).over V).over W) AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ V : Over U, ∀ W : Over V,
  (((J.over U).over V).over W).WEqualsLocallyBijective
    AddCommGrpCat.{max u v}]

/-- Internal Hom from a finitely presented source to a coherent target is coherent when the
canonical restriction comparisons are invertible. -/
@[stacks 01CQ "coherence"]
theorem isCoherentOfOverComparison
    (F G : ringedSiteModuleCategory J O)
    [F.IsFinitePresentation] [G.IsCoherent]
    [∀ U : C, (SheafOfModules.overFunctor (ringSheaf J O) U).LaxMonoidal]
    [∀ U : C, IsIso (overComparison O U F G)] :
    ((ihom F).obj G).IsCoherent := sorry

/-- Internal Hom from a finitely presented source to a coherent target is coherent when every
slice restriction preserves internal Hom. -/
@[stacks 01CQ "coherence from preservation"]
theorem isCoherentOfPreservesOver
    (F G : ringedSiteModuleCategory J O)
    [F.IsFinitePresentation] [G.IsCoherent]
    [∀ U : C, (SheafOfModules.overFunctor (ringSheaf J O) U).LaxMonoidal]
    [∀ U : C, CategoryTheory.Functor.LaxMonoidal.PreservesInternalHom
      (SheafOfModules.overFunctor (ringSheaf J O) U)] :
    ((ihom F).obj G).IsCoherent := sorry

end Coherent

end SheafOfModules.RingedSite.InternalHom
