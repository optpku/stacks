/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LocalRepresentation
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Local homotopy and lifting for strictly perfect complexes

The cover-wise predicates in this file are the reusable ringed-site layer.  They are independent
of the presentation of a ringed space as an opens site; the corresponding open-cover views live
in the ringed-space facade.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open RingedSite (ModuleCat)
open RingedSite.Hom

noncomputable section

universe u v w

namespace RingedSite.CochainComplex

variable {X : RingedSite.{u, v, w}}
variable [UnivLE.{max u v, w}]

/- The cover-wise lifting predicate is kept separate from the null-homotopy predicate so that
   later mapping-cone and descent arguments can use it without unfolding either presentation. -/
/-- A morphism `α : E ⟶ F` locally lifts through `f : G ⟶ F` at `U` when, on every member of a
cover of `U`, there is a lift whose composite with the restricted `f` is homotopic to the
restricted `α`. -/
@[stacks 08FQ "cover-wise local lifting"]
def IsLocallyLiftableAt
    {E F G : _root_.CochainComplex (ModuleCat.{w} X) ℤ}
    (α : E ⟶ F) (f : G ⟶ F) (U : X.carrier) : Prop :=
  ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
    ∃ β : (localizedRestrictionComplex.{w} X I.Y).obj E ⟶
        (localizedRestrictionComplex.{w} X I.Y).obj G,
      Nonempty (Homotopy
        ((localizedRestrictionComplex.{w} X I.Y).map α)
        (β ≫ (localizedRestrictionComplex.{w} X I.Y).map f))

omit [UnivLE.{max u v, w}] in
/-- The cover-wise lifting predicate is definitionally the displayed restriction-and-homotopy
criterion. -/
theorem isLocallyLiftableAt_iff
    {E F G : _root_.CochainComplex (ModuleCat.{w} X) ℤ}
    (α : E ⟶ F) (f : G ⟶ F) (U : X.carrier) :
    IsLocallyLiftableAt α f U ↔
      ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
        ∃ β : (localizedRestrictionComplex.{w} X I.Y).obj E ⟶
            (localizedRestrictionComplex.{w} X I.Y).obj G,
          Nonempty (Homotopy
            ((localizedRestrictionComplex.{w} X I.Y).map α)
            (β ≫ (localizedRestrictionComplex.{w} X I.Y).map f)) := sorry

namespace IsStrictlyPerfect

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{w}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.carrier, HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X.carrier,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/- The bounds and vanishing hypotheses below are intentionally stated at the homology-map level.
   This keeps the API usable for any later source of acyclic or truncated complexes. -/
namespace NullHomotopy
/-- A strictly perfect source maps locally null-homotopically into an acyclic complex. -/
@[stacks 08FP "strictly perfect source and acyclic target"]
theorem at_of_acyclic
    {E F : _root_.CochainComplex (ModuleCat.{w} X) ℤ}
    (hE : IsStrictlyPerfect E) (α : E ⟶ F) (hF : F.Acyclic) (U : X.carrier) :
    IsLocallyNullHomotopicAt α U := sorry

/-- A strictly perfect source bounded below by `a` maps locally null-homotopically into a complex
whose homology vanishes in all degrees at least `a`. -/
@[stacks 08FP "bounded-below local null homotopy"]
theorem at_of_isStrictlyGE
    {E F : _root_.CochainComplex (ModuleCat.{w} X) ℤ} (a : ℤ)
    (hE : IsStrictlyPerfect E) (hE_ge : E.IsStrictlyGE a) (α : E ⟶ F)
    (hF : ∀ i : ℤ, a ≤ i → IsZero (F.homology i)) (U : X.carrier) :
    IsLocallyNullHomotopicAt α U := sorry

end NullHomotopy

namespace Lift
/-- A bounded-below strictly perfect source locally lifts through a map that is an isomorphism
above `a` and an epimorphism in degree `a`, up to homotopy. -/
@[stacks 08FQ "bounded-below local lifting"]
theorem at_of_isStrictlyGE
    {E F G : _root_.CochainComplex (ModuleCat.{w} X) ℤ} (a : ℤ)
    (hE : IsStrictlyPerfect E) (hE_ge : E.IsStrictlyGE a)
    (α : E ⟶ F) (f : G ⟶ F)
    (hf_iso : ∀ j : ℤ, a < j → IsIso (HomologicalComplex.homologyMap f j))
    (hf_epi : Epi (HomologicalComplex.homologyMap f a)) (U : X.carrier) :
    IsLocallyLiftableAt α f U := sorry

end Lift

end IsStrictlyPerfect

end RingedSite.CochainComplex
