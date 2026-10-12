/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.WeaklyContractible
public import ReasLib.CategoryTheory.Sites.Cohomology.Exact
public import ReasLib.CategoryTheory.Sites.Torsor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Consequences of weak contractibility

This leaf collects the reusable consequences of a weakly contractible object.  The defining
section-surjectivity class remains in `WeaklyContractible`; exactness, cohomology vanishing, and
torsor sections are separate bridges so downstream developments can import only this API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.IsWeaklyContractible

variable {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}

/-- Lemma 21.51.1 (0946) (1): weak contractibility makes the abelian sections functor exact. -/
@[stacks 0946 "exact sections over a weakly contractible object"]
theorem sectionsFunctor_exact
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (U : C) [J.IsWeaklyContractible U] :
    exactFunctor (Sheaf J AddCommGrpCat.{max u v}) AddCommGrpCat.{max u v}
      (siteAbelianSectionsFunctor J U) := sorry

/-- Lemma 21.51.1 (0946) (2): positive objectwise cohomology vanishes on a weakly contractible
object. -/
@[stacks 0946 "higher cohomology vanishing over a weakly contractible object"]
theorem higherCohomology_isZero
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasExt.{max u v} (Sheaf J AddCommGrpCat.{max u v})]
    (U : C) [J.IsWeaklyContractible U]
    (F : Sheaf J AddCommGrpCat.{max u v}) {q : ℕ} (hq : 0 < q) :
    IsZero (F.H' q U) := sorry

/-- Lemma 21.51.1 (0946) (3): a torsor has a section over every weakly contractible object. -/
@[stacks 0946 "torsor sections over a weakly contractible object"]
theorem torsor_sections_nonempty
    (U : C) [J.IsWeaklyContractible U]
    (G : Sheaf J GrpCat.{max u v}) (P : Sheaf.Torsor G) :
    Nonempty (P.Sections U) := sorry

end CategoryTheory.GrothendieckTopology.IsWeaklyContractible
