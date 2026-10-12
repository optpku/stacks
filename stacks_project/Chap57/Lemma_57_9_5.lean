/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.TruncationSplit
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped DerivedCategory.CohomologyIn

universe u

/- Lemma 57.9.5: if a bounded coherent complex on a regular Noetherian scheme has a cohomology
gap of the dimension, then it splits as the biproduct of its lower and upper truncations. -/
@[stacks 0FZ4] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.truncation_split_of_cohomology_vanishing :
    ∀ {X : Scheme.{u}} [IsNoetherian X] [Scheme.Regular X]
    (d : ℕ) (h_dimension : topologicalKrullDim X = d)
    (K : Dᵇ[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf])
    (a : ℤ)
    (hvanish : ∀ i : ℤ, a < i → i < a + (d : ℤ) →
      IsZero ((DerivedCategory.Bounded.homologyFunctor X.Modules i).obj K.obj)),
    ∃ e : K.obj.obj ≅
        (DerivedCategory.TStructure.t.truncLE a).obj K.obj.obj ⊞
          (DerivedCategory.TStructure.t.truncGE (a + (d : ℤ))).obj K.obj.obj,
      ((DerivedCategory.TStructure.t.truncLEι a).app K.obj.obj) ≫ e.hom = biprod.inl ∧
        e.hom ≫ biprod.snd =
          (DerivedCategory.TStructure.t.truncGEπ (a + (d : ℤ))).app K.obj.obj)
