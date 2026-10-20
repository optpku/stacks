/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sigma.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeFunctor
public import ReasLib.AlgebraicGeometry.QuotientStack.AbstractGroup
public import ReasLib.AlgebraicGeometry.Scheme.GroupAction.FixedLocus
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Coproduct of fixed-locus quotient categories

The sigma-category of the quotient categories of residual actions carries its canonical
projection to schemes over the base.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.QuotientStack.AbstractGroup
open AlgebraicGeometry.Scheme.GroupAction.FixedLocus

noncomputable section

universe u

namespace AlgebraicGeometry.QuotientStack.InertiaCoprod

variable {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}

/-- The quotient stack of the residual action on the fixed locus of a group element. -/
def fixedQuotient (ρ : G →* Aut X) (g : G) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  stack (((ofOverFunctor S).mapAut _).comp (residual ρ g))

/-- The projection of a fixed-locus quotient is the forgetful functor of its residual action. -/
theorem fixedQuotient_p (ρ : G →* Aut X) (g : G) :
    (fixedQuotient ρ g).p = forget (((ofOverFunctor S).mapAut _).comp (residual ρ g)) :=
  rfl

/-- The sigma-category of quotient objects for all fixed loci of the action. -/
abbrev CoprodObj (ρ : G →* Aut X) :=
  Σ g : G, Obj (((ofOverFunctor S).mapAut _).comp (residual ρ g))

/-- Insert a quotient object into the summand indexed by its fixed group element. -/
def ofSummand (ρ : G →* Aut X) (g : G)
    (ξ : Obj (((ofOverFunctor S).mapAut _).comp (residual ρ g))) : CoprodObj ρ :=
  (CategoryTheory.Sigma.incl g).obj ξ

/-- Inserting a summand retains its index and quotient object. -/
theorem ofSummand_spec (ρ : G →* Aut X) (g : G)
    (ξ : Obj (((ofOverFunctor S).mapAut _).comp (residual ρ g))) :
    (ofSummand ρ g ξ).1 = g ∧ (ofSummand ρ g ξ).2 = ξ :=
  ⟨rfl, rfl⟩

/-- The projection from the sigma-category of fixed-locus quotients to schemes over the base. -/
def p (ρ : G →* Aut X) : CoprodObj ρ ⥤ Over S :=
  CategoryTheory.Sigma.desc fun g ↦
    forget (((ofOverFunctor S).mapAut _).comp (residual ρ g))

/-- The coproduct projection retains the test scheme of a quotient object. -/
theorem p_obj {ρ : G →* Aut X} (ξ : CoprodObj ρ) :
    (p ρ).obj ξ = ξ.2.U :=
  rfl

/-- The coproduct projection takes a summand morphism to its underlying scheme map. -/
theorem p_map {ρ : G →* Aut X} {g : G}
    {ξ ξ' : Obj (((ofOverFunctor S).mapAut _).comp (residual ρ g))} (α : ξ ⟶ ξ') :
    (p ρ).map (CategoryTheory.Sigma.SigmaHom.mk α) = α.f :=
  rfl

/-- The coproduct projection of fixed-locus quotient categories is fibered in groupoids. -/
instance instIsFiberedInGroupoids (ρ : G →* Aut X) :
    Functor.IsFibered.InGroupoids (p ρ) :=
  sorry

end AlgebraicGeometry.QuotientStack.InertiaCoprod
