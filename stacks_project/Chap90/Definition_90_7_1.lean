/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]

/- Definition 90.7.1 (1): a formal object of a category F cofibered in groupoids
over C_Λ is a triple ξ = (R, ξ_n, f_n) with R an object of hat C_Λ, objects
ξ_n of F over its maximal-adic truncations, and successor morphisms lying over
the truncation projections. Lean stage n represents the source's positive-power
stage n + 1, with base R ⧸ maximalIdeal R ^ (n + 1). Its transition from Lean
stage n + 1 to n lies over R ⧸ maximalIdeal R ^ (n + 2) ⟶
R ⧸ maximalIdeal R ^ (n + 1). This is owned by FormalObject. -/
@[stacks 06H3] #check (FormalObject p : Type (max (u + 1) v))

/- Definition 90.7.1 (2): a morphism a : ξ ⟶ η of formal objects consists of
a map a_0 : R ⟶ S in hat C_Λ and stage morphisms of F lying over the induced
maps R ⧸ maximalIdeal R ^ (n + 1) ⟶ S ⧸ maximalIdeal S ^ (n + 1) in the
positive-power indexing above. The successor squares commute:
ξ.system.stepMap n ≫ a.app n = a.app (n + 1) ≫ η.system.stepMap n.
This is owned by FormalObject.Hom. -/
@[stacks 06H3] #check
  (FormalObject.Hom (p := p) : FormalObject p → FormalObject p → Type (max u v))

/- Definition 90.7.1 (3): formal objects and their compatible morphisms form
a category, with componentwise identities and composition. -/
@[stacks 06H3] #check (FormalObject.category (p := p) : Category.{max u v} (FormalObject p))
