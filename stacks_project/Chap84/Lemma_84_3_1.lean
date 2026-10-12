/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Basic
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap73.Lemma_73_4_7_Relocalization
public import stacks_project.Chap73.Lemma_73_7_8_Topology
public import stacks_project.Chap73.Lemma_73_8_8_Site

/-!
# Lemma 84.3.1

The inclusion of big sites `(Sch/S)_τ ⟶ (Spaces/S)_τ` along `ofOverFunctor S`
is special cocontinuous for `τ ∈ {étale, fppf, ph}`, and therefore identifies
the corresponding sheaf topoi.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 84.3.1 (1): the inclusion `(Sch/S)_étale ⟶ (Spaces/S)_étale` given by
`ofOverFunctor S` is special cocontinuous. -/
@[stacks 0DFV]
instance ofOverFunctor_isSpecialCocontinuous_etale (S : Scheme.{u}) :
    (ofOverFunctor S).IsSpecialCocontinuous (Scheme.etaleTopology.over S)
      etaleTopology := sorry

/-- Lemma 84.3.1 (2): the cocontinuous direct image along `ofOverFunctor S` identifies
étale sheaf topoi of schemes over `S` with étale sheaf topoi of algebraic spaces over `S`. -/
@[stacks 0DFV]
instance ofOverFunctor_directImage_isEquivalence_etale (S : Scheme.{u})
    [∀ P : (Over S)ᵒᵖ ⥤ Type (u + 1),
      (ofOverFunctor S).op.HasPointwiseRightKanExtension P] :
    ((ofOverFunctor S).sheafPushforwardCocontinuous (Type (u + 1))
      (Scheme.etaleTopology.over S) etaleTopology).IsEquivalence := sorry

/-- Lemma 84.3.1 (3): the inclusion `(Sch/S)_fppf ⟶ (Spaces/S)_fppf` given by
`ofOverFunctor S` is special cocontinuous. -/
@[stacks 0DFV]
instance ofOverFunctor_isSpecialCocontinuous_fppf (S : Scheme.{u}) :
    (ofOverFunctor S).IsSpecialCocontinuous (Scheme.fppfTopology.over S)
      (fppfTopology S) := sorry

/-- Lemma 84.3.1 (4): the cocontinuous direct image along `ofOverFunctor S` identifies
fppf sheaf topoi of schemes over `S` with fppf sheaf topoi of algebraic spaces over `S`. -/
@[stacks 0DFV]
instance ofOverFunctor_directImage_isEquivalence_fppf (S : Scheme.{u})
    [∀ P : (Over S)ᵒᵖ ⥤ Type (u + 1),
      (ofOverFunctor S).op.HasPointwiseRightKanExtension P] :
    ((ofOverFunctor S).sheafPushforwardCocontinuous (Type (u + 1))
      (Scheme.fppfTopology.over S) (fppfTopology S)).IsEquivalence := sorry

/-- Lemma 84.3.1 (5): the inclusion `(Sch/S)_ph ⟶ (Spaces/S)_ph` given by
`ofOverFunctor S` is special cocontinuous. -/
@[stacks 0DFV]
instance ofOverFunctor_isSpecialCocontinuous_ph (S : Scheme.{u}) :
    (ofOverFunctor S).IsSpecialCocontinuous (Scheme.bigPhSite S) (phTopology S) := sorry

/-- Lemma 84.3.1 (6): the cocontinuous direct image along `ofOverFunctor S` identifies
ph sheaf topoi of schemes over `S` with ph sheaf topoi of algebraic spaces over `S`. -/
@[stacks 0DFV]
instance ofOverFunctor_directImage_isEquivalence_ph (S : Scheme.{u})
    [∀ P : (Over S)ᵒᵖ ⥤ Type (u + 1),
      (ofOverFunctor S).op.HasPointwiseRightKanExtension P] :
    ((ofOverFunctor S).sheafPushforwardCocontinuous (Type (u + 1))
      (Scheme.bigPhSite S) (phTopology S)).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace
