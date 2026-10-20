module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat.Sequential
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Unbounded.Acyclic
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Cohomology
public import ReasLib.CategoryTheory.DerivedCategory.Limit.RightDerived
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.DerivedFunctor.Grothendieck
public import ReasLib.CategoryTheory.InverseSystem.Milnor.CochainComplex
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.AddCommGrp
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.Envelope

/-!
# Derived Sequential Limits of Abelian Groups

This leaf gives the reusable abelian-group specialization of the sequential derived-limit API.
The textbook-facing results are stated using the canonical `DerivedLimit` and `Functor` owners;
the explicit Milnor cochain complex is kept as concrete data rather than replaced by an
unspecified derived-limit witness.
@stack 07KW
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape

noncomputable section

universe v

namespace CategoryTheory.DerivedLimit

namespace RightDerived

/-- Lemma 15.87.1 (1) [07KW]: the ordinary `p`th right-derived functor of sequential inverse
limit on abelian groups vanishes for every `p > 1`. -/
@[stacks 07KW]
theorem isZero_of_one_lt
    (A : SequentialInverseSystem AddCommGrpCat.{v})
    (p : ℕ) (hp : 1 < p) :
    IsZero ((rightDerived (A := AddCommGrpCat.{v}) p).obj A) := sorry

end RightDerived

namespace RightAcyclic

/-- Lemma 15.87.1 (3), together with the finite-prefix Mittag-Leffler envelope: every sequential
system of abelian groups embeds into one that is bounded right acyclic for inverse limit. -/
@[stacks 07KW]
instance hasMonoEmbedding :
    CategoryTheory.ObjectProperty.HasMonoEmbedding
      (Functor.RightAcyclic.Bounded
        (CategoryTheory.Limits.lim :
          SequentialInverseSystem AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v})) := sorry

end RightAcyclic

namespace Vanishes

/-- The degree-two vanishing bound for sequential inverse limit, packaged in the form consumed by
the generic unbounded right-acyclic resolution API. -/
theorem inDegree_two :
    Functor.RightDerived.Bounded.Vanishes.inDegree
      (CategoryTheory.Limits.lim :
        SequentialInverseSystem AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v}) 2 := sorry

end Vanishes

namespace Milnor

/-- Lemma 15.87.1 (2) [07KW]: for a degree-zero inverse system of abelian groups, the canonical
derived inverse limit is represented by the explicit two-term Milnor cochain complex. -/
@[stacks 07KW]
theorem singleIso
    (A : SequentialInverseSystem AddCommGrpCat.{v}) :
    Nonempty
      (DerivedCategory.Q.obj A.milnorCochainComplex ≅
        (DerivedLimit.functor AddCommGrpCat.{v}).obj
          ((DerivedCategory.singleFunctor (SequentialInverseSystem AddCommGrpCat.{v}) 0).obj A)) := sorry

end Milnor

end CategoryTheory.DerivedLimit

namespace CategoryTheory.SequentialInverseSystem.IsMittagLeffler

namespace Limit

/-- Lemma 15.87.1 (3) [07KW]: a Mittag-Leffler tower of abelian groups is right acyclic for the
ordinary inverse-limit functor. -/
@[stacks 07KW]
theorem rightAcyclic
    (A : SequentialInverseSystem AddCommGrpCat.{v})
    (hA : A.IsMittagLeffler) :
    Functor.RightAcyclic.Bounded
      (CategoryTheory.Limits.lim :
        SequentialInverseSystem AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v}) A := sorry

end Limit

/-- The first derived inverse limit of a Mittag-Leffler tower of abelian groups is zero. -/
theorem r1_isZero
    (A : SequentialInverseSystem AddCommGrpCat.{v})
    (hA : A.IsMittagLeffler) :
    IsZero (CategoryTheory.DerivedLimit.R1 A) := sorry

end CategoryTheory.SequentialInverseSystem.IsMittagLeffler

namespace CategoryTheory.DerivedLimit

end CategoryTheory.DerivedLimit
