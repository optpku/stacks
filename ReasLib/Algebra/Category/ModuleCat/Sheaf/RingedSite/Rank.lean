module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteLocallyFree
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction and Cover API for Fixed-Rank Module Sheaves

The fixed-rank predicate is owned for module sheaves over an arbitrary sheaf of rings. This file
contains its restriction API and its cover-based characterization on commutative ringed sites.
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

namespace SheafOfModules.IsFiniteLocallyFreeOfRank

section Over

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Finite local freeness of a fixed rank is preserved by restriction to a slice site. -/
@[stacks 0409 "restriction stability"]
instance over (r : ℕ) (M : SheafOfModules.{w} R) (U : C)
    [IsFiniteLocallyFreeOfRank r M]
    [∀ V : Over U, HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
    [∀ V : Over U,
      ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    IsFiniteLocallyFreeOfRank r (M.over U) := sorry

section RingedSite

variable {O : Sheaf J CommRingCat.{w}}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Fixed rank after restriction, specialized to the canonical module category on the localized
commutative ringed site. This bridge fixes the coefficient owner expected by ringed-site APIs. -/
@[stacks 0409 "commutative ringed-site restriction stability"]
instance overRingedSite
    (r : ℕ) (M : SheafOfModules.RingedSite.ringedSiteModuleCategory J O) (U : C)
    [IsFiniteLocallyFreeOfRank r M]
    [∀ V : Over U, HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
    [∀ V : Over U,
      ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    IsFiniteLocallyFreeOfRank r
      (M.over U : SheafOfModules.RingedSite.ringedSiteModuleCategory (J.over U) (O.over U)) := sorry

end RingedSite

end Over

section Cover

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{w}}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- On a commutative ringed site, fixed-rank local-generator data is equivalent to the textbook
description by rank-`r` free trivializations after a cover of every slice object. -/
@[stacks 0409 "cover characterization", stacks 01C6 "(3), cover characterization"]
theorem iff_existsCover (r : ℕ)
    (M : SheafOfModules.RingedSite.ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    IsFiniteLocallyFreeOfRank r M ↔
      ∀ U : C,
        ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
          ∀ i : I,
            Nonempty
              (((M.over U).over (X i)) ≅
                (SheafOfModules.free (ULift.{w} (Fin r)) :
                  SheafOfModules.RingedSite.ringedSiteModuleCategory.{max u v, v, w, w}
                    ((J.over U).over (X i)) ((𝒪.over U).over (X i)))) := sorry

end Cover

end SheafOfModules.IsFiniteLocallyFreeOfRank
