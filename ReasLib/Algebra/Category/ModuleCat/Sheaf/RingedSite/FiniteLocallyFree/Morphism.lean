/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Rank
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms between finite locally free module sheaves

The same-rank epimorphism criterion is intrinsic to module sheaves on a commutative ringed site;
it does not depend on points or on a topological-space presentation of the site.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

universe u v w

namespace SheafOfModules.IsFiniteLocallyFreeOfRank

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {O : Sheaf J CommRingCat.{w}}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Lemma 17.14.5 (089Q): a morphism between finite locally free module sheaves of the same rank
on a commutative ringed site is an isomorphism exactly when it is an epimorphism. -/
@[stacks 089Q]
theorem isIso_iff_epi {r : ℕ}
    {F G : ringedSiteModuleCategory.{u, v, w, w} J O}
    [_root_.SheafOfModules.IsFiniteLocallyFreeOfRank (R := ringSheaf J O) r F]
    [_root_.SheafOfModules.IsFiniteLocallyFreeOfRank (R := ringSheaf J O) r G]
    (f : F ⟶ G) :
    IsIso f ↔ Epi f := sorry

/-- An epimorphism between finite locally free module sheaves of the same rank on a commutative
ringed site is an isomorphism. -/
@[stacks 089Q "epimorphism criterion"]
theorem isIso_of_epi {r : ℕ}
    {F G : ringedSiteModuleCategory.{u, v, w, w} J O}
    [_root_.SheafOfModules.IsFiniteLocallyFreeOfRank (R := ringSheaf J O) r F]
    [_root_.SheafOfModules.IsFiniteLocallyFreeOfRank (R := ringSheaf J O) r G]
    (f : F ⟶ G) [Epi f] :
    IsIso f := sorry

end SheafOfModules.IsFiniteLocallyFreeOfRank
