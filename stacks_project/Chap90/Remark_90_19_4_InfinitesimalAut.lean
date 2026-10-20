/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Predeformation
import StacksCheckRecall

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor Fiber

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsPredeformationCategory p]
variable (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
variable (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
variable [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]

/- Remark 90.19.4: the infinitesimal subgroup is the full automorphism group of
the dual-number pushforward. -/
@[stacks 06JS]
#check (CategoryTheory.Functor.infinitesimalAutomorphismsAt_eq_top p x0 x0' φ :
  infinitesimalAutomorphismsAt p x0 x0' φ = (⊤ : Subgroup (Aut x0')))
