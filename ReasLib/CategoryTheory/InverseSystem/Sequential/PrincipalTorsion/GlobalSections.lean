/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import ReasLib.CategoryTheory.InverseSystem.Sequential.PrincipalTorsion
public import ReasLib.Algebra.Category.ModuleCat.Topology.Limit
public import ReasLib.RingTheory.Ideal.Principal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Global sections of principal torsion systems

Applying global sections to a principal torsion inverse system produces the canonical module
tower used in finiteness, regularity, and projection-kernel statements.  The tower view is kept
in this ReasLib leaf so topological-space and other site presentations share the same API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped PrincipalIdeal

noncomputable section

universe u v w

namespace CategoryTheory.SequentialInverseSystem.PrincipalTorsion.GlobalSections

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {A : Type w} [CommRing A]
variable [HasWeakSheafify J (ModuleCat A)]
variable [HasGlobalSectionsFunctor J (ModuleCat A)]

/-- The module-valued global-sections tower associated with a sequential system of module sheaves. -/
@[stacks 0BLB "global-sections tower of a principal torsion system"]
abbrev tower
    (F : SequentialInverseSystem (Sheaf J (ModuleCat A))) :
    SequentialInverseSystem (ModuleCat A) :=
  F ⋙ Sheaf.Γ J (ModuleCat A)

/-- Lemma 20.36.3 (1) (0BLB): if the base ring is Noetherian and complete for `(f)`, and
the first global-sections module is finite, then the global-sections limit of a principal torsion
tower is finite. -/
@[stacks 0BLB "finite global-sections limit"]
theorem limit_finite
    (f : A) (F : SequentialInverseSystem (Sheaf J (ModuleCat A)))
    [IsNoetherianRing A]
    [IsAdicComplete ((f) : Ideal A) A]
    (h₁ : Module.Finite A
      ((Sheaf.Γ J (ModuleCat A)).obj (F.obj (op 1))))
    (hF : PrincipalTorsion.IsPresented f F) :
    Module.Finite A (limit (tower F) : ModuleCat A) := sorry

/-- Lemma 20.36.3 (2) (0BLB): multiplication by `f` on the global-sections limit of a
principal torsion tower is regular. -/
@[stacks 0BLB "regular scalar on the global-sections limit"]
theorem limit_isSMulRegular
    (f : A) (F : SequentialInverseSystem (Sheaf J (ModuleCat A)))
    (hF : PrincipalTorsion.IsPresented f F) :
    IsSMulRegular (limit (tower F) : ModuleCat A) f := sorry

/-- Lemma 20.36.3 (3) (0BLB): the kernel of projection from the global-sections limit to
the first stage is the principal submodule `(f) • ⊤`. -/
@[stacks 0BLB "first-stage projection kernel"]
theorem projectionKernel_eq_smul_top
    (f : A) (F : SequentialInverseSystem (Sheaf J (ModuleCat A)))
    (hF : PrincipalTorsion.IsPresented f F) :
    Functor.limitKernel (tower F) (op 1) =
      ((f) : Ideal A) • (⊤ : Submodule A (limit (tower F) : ModuleCat A)) := sorry

end CategoryTheory.SequentialInverseSystem.PrincipalTorsion.GlobalSections
