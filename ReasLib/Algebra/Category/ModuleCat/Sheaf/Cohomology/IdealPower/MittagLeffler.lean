module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology.IdealPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology.IdealPower.EventualRange
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
import Mathlib.Tactic.CrossRefAttribute

/-!
# Mittag-Leffler consequences of ideal-power cohomology

This leaf owns the two stabilization statements used by the ideal-power cohomology arguments.
The first statement uses a one-parameter presentation of the quotient tower.  The second uses a
two-parameter family and its stable-image (eventual-range) pieces.  The positive-indexed
presentation is the canonical owner of the degree shift: its `toSequential` reindexing is the
ordinary tower `n ↦ F (n + 1)` used in site cohomology.

The hypotheses are deliberately expressed through the canonical `Action` classes.  Those classes
own the associated-graded module and its homogeneous computation rule, so callers do not need to
rebuild a `Module`, a `SetLike.GradedSMul`, or a local scalar instance at every application site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.PNatInverseSystem.IdealPower

noncomputable section

universe u v w

namespace CategoryTheory.SiteModuleCohomology.IdealPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type w} [CommRing A]
variable [HasWeakSheafify J (ModuleCat.{max u v w} A)]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
variable [J.HasSheafCompose
  (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})]

/- The positive presentation is the source-facing one-parameter ideal-power quotient tower. -/

/-- Lemma 21.22.1 (0GYQ): Noetherianity of the graded exact-degree cohomology of a presented
ideal-power quotient tower forces its site-cohomology tower to satisfy the Mittag-Leffler
condition.  The `Action` instance supplies the canonical `gr_I(A)`-module structure and the
homogeneous multiplication rule. -/
@[stacks 0GYQ]
theorem isMittagLeffler_of_isNoetherian
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    (P : PNatInverseSystem.IdealPower.Presentation I F) (p : ℕ)
    [Action P p]
    [IsNoetherian (Ideal.AssociatedGraded.ring I)
      (SiteModuleCohomology.directSum (terms P) p)] :
    SequentialInverseSystem.IsMittagLeffler
      (siteModuleCohomologyTower F.toSequential p) := sorry

end CategoryTheory.SiteModuleCohomology.IdealPower

namespace CategoryTheory.SiteModuleCohomology.IdealPower.Eventual

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type w} [CommRing A]
variable [HasWeakSheafify J (ModuleCat.{max u v w} A)]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
variable [J.HasSheafCompose
  (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})]

/-- Lemma 21.22.2 (0GYR): if the graded direct sum of the stable ideal-power cohomology pieces is
Noetherian for its canonical associated-graded action, then the ambient site-cohomology tower is
Mittag-Leffler.  The two-parameter `Family` records the compatible fixed-right short exact rows;
`Eventual.Action` records the induced action on the stable images. -/
@[stacks 0GYR]
theorem isMittagLeffler_of_isNoetherian
    {I : Ideal A}
    {F : PNatInverseSystem (Sheaf J (ModuleCat.{max u v w} A))}
    (P : PNatInverseSystem.IdealPower.Family I F) (p : ℕ)
    [Action P p]
    [IsNoetherian (Ideal.AssociatedGraded.ring I) (directSum P p)] :
    SequentialInverseSystem.IsMittagLeffler
      (siteModuleCohomologyTower F.toSequential p) := sorry

end CategoryTheory.SiteModuleCohomology.IdealPower.Eventual

end
