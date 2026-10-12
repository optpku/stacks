/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.DeltaFunctor
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

/- Lemma 22.23.1 (09L0): the canonical functor from right differential graded modules over a DG
algebra to their derived category is a delta functor. -/
@[stacks 09L0]
#check
  (DifferentialGradedModule.Derived.Delta.functor A :
    DeltaFunctor (DifferentialGradedModule.{u, v} A)
      (DifferentialGradedModule.Derived.Category A))

/- The underlying functor is the canonical localization `Derived.fromModules A`. -/
#check @DifferentialGradedModule.Derived.Delta.functor_toFunctor

/- Its connecting morphism is the mapping-cone boundary of a short exact DG-module sequence. -/
#check @DifferentialGradedModule.Derived.Delta.functor_δ

/- The owner exposes naturality and distinguishedness independently for downstream use. -/
#check @DifferentialGradedModule.Derived.Delta.δ_naturality
#check @DifferentialGradedModule.Derived.Delta.triangle_distinguished
