/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Big
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.Site
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Basic
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous

/-!
# Comparison of big sites of schemes and algebraic spaces

The inclusion of schemes over a base scheme into algebraic spaces over that
base is special cocontinuous for the étale, fppf, and ph topologies, and its
cocontinuous direct image induces equivalences of sheaf categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every presheaf valued in `Type (u + 1)` on schemes over `S` has a pointwise
right Kan extension along the opposite of the inclusion into algebraic spaces. -/
instance ofOverFunctor_op_hasPointwiseRightKanExtension (S : Scheme.{u})
    (P : (Over S)ᵒᵖ ⥤ Type (u + 1)) :
    (ofOverFunctor S).op.HasPointwiseRightKanExtension P :=
  fun _ ↦ inferInstance

/-- The inclusion of schemes over `S` into algebraic spaces over `S` is special
cocontinuous for the big étale topologies. -/
@[stacks 0DFV]
instance ofOverFunctor_isSpecialCocontinuous_etale (S : Scheme.{u}) :
    (ofOverFunctor S).IsSpecialCocontinuous (Scheme.etaleTopology.over S)
      etaleTopology := sorry

/-- Cocontinuous direct image along the inclusion of schemes over `S` into
algebraic spaces over `S` is an equivalence of big étale sheaf categories. -/
@[stacks 0DFV]
instance ofOverFunctor_directImage_isEquivalence_etale (S : Scheme.{u}) :
    ((ofOverFunctor S).sheafPushforwardCocontinuous (Type (u + 1))
      (Scheme.etaleTopology.over S) etaleTopology).IsEquivalence :=
  CategoryTheory.Functor.IsSpecialCocontinuous.directImage_isEquivalence (ofOverFunctor S)

/-- The inclusion of schemes over `S` into algebraic spaces over `S` is special
cocontinuous for the big fppf topologies. -/
@[stacks 0DFV]
instance ofOverFunctor_isSpecialCocontinuous_fppf (S : Scheme.{u}) :
    (ofOverFunctor S).IsSpecialCocontinuous (Scheme.fppfTopology.over S)
      (fppfTopology S) := sorry

/-- Cocontinuous direct image along the inclusion of schemes over `S` into
algebraic spaces over `S` is an equivalence of big fppf sheaf categories. -/
@[stacks 0DFV]
instance ofOverFunctor_directImage_isEquivalence_fppf (S : Scheme.{u}) :
    ((ofOverFunctor S).sheafPushforwardCocontinuous (Type (u + 1))
      (Scheme.fppfTopology.over S) (fppfTopology S)).IsEquivalence :=
  CategoryTheory.Functor.IsSpecialCocontinuous.directImage_isEquivalence (ofOverFunctor S)

/-- The inclusion of schemes over `S` into algebraic spaces over `S` is special
cocontinuous for the big ph topologies. -/
@[stacks 0DFV]
instance ofOverFunctor_isSpecialCocontinuous_ph (S : Scheme.{u}) :
    (ofOverFunctor S).IsSpecialCocontinuous (Scheme.bigPhSite S) (phTopology S) := sorry

/-- Cocontinuous direct image along the inclusion of schemes over `S` into
algebraic spaces over `S` is an equivalence of big ph sheaf categories. -/
@[stacks 0DFV]
instance ofOverFunctor_directImage_isEquivalence_ph (S : Scheme.{u}) :
    ((ofOverFunctor S).sheafPushforwardCocontinuous (Type (u + 1))
      (Scheme.bigPhSite S) (phTopology S)).IsEquivalence :=
  CategoryTheory.Functor.IsSpecialCocontinuous.directImage_isEquivalence (ofOverFunctor S)

end AlgebraicGeometry.AlgebraicSpace
