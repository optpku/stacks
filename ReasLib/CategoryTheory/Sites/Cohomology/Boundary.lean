/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import ReasLib.CategoryTheory.Sites.Cohomology.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Global boundary maps

The connecting morphism of a short exact sequence of additive sheaves is a concrete map on
global sections.  This leaf owns that map independently of any ringed-space or square-zero
specialization; those specializations only supply a scalar action on its target.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor J AddCommGrpCat.{w}]
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]

/-- The degree-one global boundary map attached to an exact short complex of additive sheaves.

The source is transported through the canonical degree-zero global-sections/`Ext` equivalence,
and the target is the degree-one sheaf cohomology of the kernel term. -/
@[stacks 0B8S "global boundary map of a short exact sequence",
  stacks 04BP "global boundary map of an exact additive-sheaf row"]
noncomputable def globalBoundary
    {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) :
    ((Sheaf.Γ J AddCommGrpCat.{w}).obj S.X₃) →ₗ[ℤ] Sheaf.H S.X₁ 1 :=
  ((Abelian.Ext.postcompOfLinear (R := ℤ) hS.extClass
      (constantIntegerSheaf J) (zero_add 1)).toAddMonoidHom.comp
    (Sheaf.globalSectionsExtZeroEquiv J S.X₃).toAddMonoidHom).toIntLinearMap

/-- The underlying additive map of `globalBoundary hS` is the Ext connecting map. -/
@[stacks 0B8S "global boundary map specification"]
theorem globalBoundary_apply
    {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (x : (Sheaf.Γ J AddCommGrpCat.{w}).obj S.X₃) :
    globalBoundary hS x =
      (Abelian.Ext.postcompOfLinear (R := ℤ) hS.extClass
        (constantIntegerSheaf J) (zero_add 1))
        ((Sheaf.globalSectionsExtZeroEquiv J S.X₃) x) := sorry

end CategoryTheory.ShortComplex.ShortExact
