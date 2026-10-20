/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.CoverLifting

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

namespace ProEt

variable {U X : Scheme.{u}}

/-- Composition with a weakly étale morphism `j : U ⟶ X` sends the small
pro-étale site of `U` to the small pro-étale site of `X`; this is the
site-level restriction functor. -/
abbrev restriction (j : U ⟶ X) [WeaklyEtale j] : U.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.map (P := @WeaklyEtale) (Q := (⊤ : MorphismProperty Scheme))
    (f := j) (inferInstance : WeaklyEtale j)

/-- Composition with a weakly étale morphism is continuous for the small
pro-étale topologies. -/
instance restriction_isContinuous (j : U ⟶ X) [WeaklyEtale j] :
    Functor.IsContinuous (restriction j) (topology U) (topology X) :=
  sorry

/-- Composition with a weakly étale morphism is cocontinuous for the small
pro-étale topologies. -/
instance restriction_isCocontinuous (j : U ⟶ X) [WeaklyEtale j] :
    Functor.IsCocontinuous (restriction j) (topology U) (topology X) :=
  sorry

end ProEt

end AlgebraicGeometry.Scheme
