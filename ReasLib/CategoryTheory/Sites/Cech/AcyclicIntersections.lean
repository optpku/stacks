/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import ReasLib.CategoryTheory.Sites.Cech.Basic
public import ReasLib.CategoryTheory.Sites.Cech.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Acyclic Čech intersections

This leaf owns the source-facing acyclic-intersection criterion for a Čech-to-site comparison.
The intersection predicate is independent of a chosen spectral-sequence implementation and is
therefore the reusable API seen by downstream developments.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {U : C} {ι : Type w} [HasFiniteProducts (Over U)]
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- A covering family has acyclic Čech intersections for `F` when all positive-degree site
cohomology objects vanish on every iterated intersection of its formal Čech coproduct. -/
@[stacks 03F7 "acyclic intersections for a Cech covering"]
def HasAcyclicCechIntersections
    (family : ι → Over U) (F : Sheaf J AddCommGrpCat.{v}) : Prop :=
  ∀ (q : ℕ+) (n : ℕ)
    (i : cechCoverIntersectionIndex (FormalCoproduct.mk ι family) n),
      IsZero (F.H' q.1 (cechCoverIntersectionObject
        (FormalCoproduct.mk ι family) n i))

/-- Project the acyclic-intersection condition to a positive degree and a chosen intersection. -/
theorem HasAcyclicCechIntersections.isZero
    {family : ι → Over U} {F : Sheaf J AddCommGrpCat.{v}}
    (hacyclic : HasAcyclicCechIntersections family F)
    {q : ℕ} (hq : 0 < q) (n : ℕ)
    (i : cechCoverIntersectionIndex (FormalCoproduct.mk ι family) n) :
    IsZero (F.H' q (cechCoverIntersectionObject
      (FormalCoproduct.mk ι family) n i)) :=
  sorry

variable [HasProducts AddCommGrpCat.{v}]
variable [HasWeakSheafify J AddCommGrpCat.{v}]
variable
  [Functor.HasRightDerivedFunctor
    ((siteAbelianSectionsFunctor J U).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{v}))]

/-- Lemma 21.10.7 (03F7): acyclic iterated intersections make every normalized positive-degree
Čech-to-site comparison an isomorphism. -/
@[stacks 03F7 "Cech comparison isomorphism from acyclic intersections"]
theorem cechCohomology_iso_siteCohomology_of_acyclic_intersections
    (family : ι → Over U) (hfamily : (J.over U).CoversTop family)
    (p : ℕ) (F : Sheaf J AddCommGrpCat.{v})
    (hacyclic : HasAcyclicCechIntersections family F)
    (f : (cechCohomologyOnSheaves J family (p + 1)).obj F ⟶ F.H' (p + 1) U)
    (hf : Cech.IsComparison family (p + 1) F f) :
    IsIso f :=
  sorry

/-- Companion projection of the acyclic-intersection comparison theorem. -/
theorem Cech.IsComparison.isIso_of_acyclic_intersections
    {family : ι → Over U} {p : ℕ} {F : Sheaf J AddCommGrpCat.{v}}
    {f : (cechCohomologyOnSheaves J family (p + 1)).obj F ⟶ F.H' (p + 1) U}
    (hf : Cech.IsComparison family (p + 1) F f)
    (hfamily : (J.over U).CoversTop family)
    (hacyclic : HasAcyclicCechIntersections family F) :
    IsIso f :=
  sorry

end CategoryTheory
