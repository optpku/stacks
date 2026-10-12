/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect
public import stacks_project.Chap75.Lemma_75_13_3_Pullback

/-!
# Perfectness along the commutative small étale-to-Zariski restriction

An object of `D(𝒪_X)` is perfect if and only if its exact derived inverse
image along the commutative universe-lifted form of `ε` from 75.4.0.1 is
perfect on the small étale site.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule
open AlgebraicGeometry.Scheme.SiteRestriction
open CategoryTheory
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

/-- Exact derived inverse image along `commSmallEtaleToZariski` preserves
perfectness. -/
theorem commSmallEtaleToZariski_isPerfect
    {X : Scheme.{u}} {E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)}
    (hE : E.IsPerfect) :
    ((commSmallEtaleToZariskiDerived X).obj E).IsPerfect :=
  sorry

/-- Perfectness of the exact derived inverse image along
`commSmallEtaleToZariski` implies perfectness of the original object of
`D(𝒪_X)`. -/
theorem commSmallEtaleToZariski_isPerfect_of_pullback
    {X : Scheme.{u}} (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)) :
    ((commSmallEtaleToZariskiDerived X).obj E).IsPerfect → E.IsPerfect :=
  sorry

/-- An object of `D(𝒪_X)` is perfect if and only if its exact derived inverse
image along `commSmallEtaleToZariski`, the commutative universe-lifted form of
`ε` from 75.4.0.1, is perfect on the small étale site. -/
theorem commSmallEtaleToZariski_isPerfect_iff
    {X : Scheme.{u}} (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)) :
    E.IsPerfect ↔ ((commSmallEtaleToZariskiDerived X).obj E).IsPerfect :=
  sorry

end AlgebraicGeometry.Scheme.SiteRestriction

