/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Sheafification.Lifted
public import stacks_project.Chap75.Lemma_75_13_3_Pullback

/-!
# m-pseudo-coherence along the commutative small étale-to-Zariski restriction

An object of `D(𝒪_X)` is `m`-pseudo-coherent if and only if its exact derived
inverse image along the commutative universe-lifted form of `ε` from 75.4.0.1
is `m`-pseudo-coherent on the small étale site.
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
`m`-pseudo-coherence. -/
theorem commSmallEtaleToZariski_isMPseudoCoherent
    {X : Scheme.{u}} {E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)}
    {m : ℤ} (hE : E.IsMPseudoCoherent m) :
    ((commSmallEtaleToZariskiDerived X).obj E).IsMPseudoCoherent m :=
  sorry

/-- `m`-pseudo-coherence of the exact derived inverse image along
`commSmallEtaleToZariski` implies `m`-pseudo-coherence of the original object of
`D(𝒪_X)`. -/
theorem commSmallEtaleToZariski_isMPseudoCoherent_of_pullback
    {X : Scheme.{u}} (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X))
    {m : ℤ} :
    ((commSmallEtaleToZariskiDerived X).obj E).IsMPseudoCoherent m →
      E.IsMPseudoCoherent m :=
  sorry

/-- An object of `D(𝒪_X)` is `m`-pseudo-coherent if and only if its exact derived
inverse image along `commSmallEtaleToZariski`, the commutative universe-lifted
form of `ε` from 75.4.0.1, is `m`-pseudo-coherent on the small étale site. -/
theorem commSmallEtaleToZariski_isMPseudoCoherent_iff
    {X : Scheme.{u}} (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X))
    (m : ℤ) :
    E.IsMPseudoCoherent m ↔
      ((commSmallEtaleToZariskiDerived X).obj E).IsMPseudoCoherent m :=
  sorry

/-- An object of `D(𝒪_X)` is pseudo-coherent if and only if its exact derived
inverse image along `commSmallEtaleToZariski` is pseudo-coherent on the small
étale site. -/
theorem commSmallEtaleToZariski_isPseudoCoherent_iff
    {X : Scheme.{u}} (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)) :
    E.IsPseudoCoherent ↔
      ((commSmallEtaleToZariskiDerived X).obj E).IsPseudoCoherent :=
  sorry

end AlgebraicGeometry.Scheme.SiteRestriction
