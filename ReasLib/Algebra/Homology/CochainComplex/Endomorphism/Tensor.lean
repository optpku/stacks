/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy
public import ReasLib.Algebra.Category.DifferentialGraded.Representable
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded
public import ReasLib.Algebra.Homology.DifferentialGradedModule.DifferentialGraded
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensoring with an Object from its Endomorphism Algebra

This file records the reusable existence theorem for the differential graded functor obtained
by tensoring modules over the endomorphism algebra of a cochain complex with that complex.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits DifferentialGradedCategory

namespace CochainComplex.Endomorphism

variable {C : Type u} [Category.{v} C] [Abelian C] [HasColimits C]

/-- Lemma 22.35.1 (09LV): for a cochain complex `K` in a cocomplete abelian category,
tensoring with `K` defines a differential graded functor from modules over `End(K)`.  It sends
the represented regular module to `K` and preserves set-indexed coproducts. -/
@[stacks 09LV]
theorem exists_tensorFunctor (K : CochainComplex C ℤ) :
    ∃ F : DgFunctor ℤ
        (DifferentialGradedModule (endomorphismDGA (R := ℤ) K))
        (CochainComplex C ℤ),
      Nonempty (F.obj (representableModule (R := ℤ) K K) ≅ K) ∧
        ∀ ι : Type w, PreservesColimitsOfShape (Discrete ι) F.mapComp := sorry

end CochainComplex.Endomorphism
