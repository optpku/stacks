/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.SelfExt
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorHom.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Unit
public import ReasLib.CategoryTheory.Pretriangulated.Functor.FullyFaithful
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Full Faithfulness of Derived Tensor Functors

This leaf specializes the compact-generator criterion to tensoring by a fixed DG bimodule. Its
public statements mention only the canonical derived categories, the represented bimodule
object, and the self-extension comparison induced by the left action.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedBimodule

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, v} R}

namespace Tensor

/-- The shifted self-Hom comparison made directly by the concrete derived tensor functor, with
its regular image identified with `N.rightDerivedObject`. -/
@[stacks 09R9 "regular self-extension map for derived tensor"]
noncomputable def regularSelfExtMap
    (N : DifferentialGradedBimodule.{u, v, v, v} A B) (k : ℤ) :
    (DifferentialGradedModule.Derived.regularObject A ⟶
        (DifferentialGradedModule.Derived.regularObject A)⟦k⟧) →
      (N.rightDerivedObject ⟶ N.rightDerivedObject⟦k⟧) :=
  (derivedFunctor N).shiftedHomMap (regularObjectIso N) (regularObjectIso N) k

/-- Bijectivity of the concrete regular self-Ext map is exactly full faithfulness on all shifts
of the regular generator. -/
@[stacks 09R9 "regular-shift criterion for derived tensor full faithfulness"]
theorem isFullyFaithfulOnSelfShifts_iff
    (N : DifferentialGradedBimodule.{u, v, v, v} A B) :
    (derivedFunctor N).IsFullyFaithfulOnSelfShifts
        (DifferentialGradedModule.Derived.regularObject A) ↔
      ∀ k : ℤ, Function.Bijective (regularSelfExtMap N k) := sorry

/-- The canonical left-action self-extension comparison controls the functorial comparison on
the regular generator. -/
@[stacks 09R9 "regular self-extension bijectivity for derived tensor"]
theorem regularSelfExtMap_bijective
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (h_selfExt : N.HasSelfExtComparison) (k : ℤ) :
    Function.Bijective (regularSelfExtMap N k) := sorry

/-- Canonical self-extension comparisons make derived tensoring fully faithful on all shifts
of the regular generator. -/
@[stacks 09R9 "derived tensor full faithfulness on regular shifts"]
theorem isFullyFaithfulOnSelfShifts_of_selfExt
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (h_selfExt : N.HasSelfExtComparison) :
    (derivedFunctor N).IsFullyFaithfulOnSelfShifts
      (DifferentialGradedModule.Derived.regularObject A) := sorry

/-- Compactness of the represented bimodule object transfers to the image of the source regular
object under derived tensoring. -/
@[stacks 09R9 "compactness of the derived tensor regular image"]
theorem regularImage_isCompact
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (h_compact : IsCompactObject N.rightDerivedObject) :
    IsCompactObject
      ((derivedFunctor N).obj (DifferentialGradedModule.Derived.regularObject A)) := sorry

/-- For the concrete derived tensor functor, compactness and shifted-Hom bijectivity on the
regular generator imply bijectivity on every Hom set; all source generator hypotheses are
canonical. -/
@[stacks 09R9 "Hom bijectivity from the derived tensor regular generator"]
theorem map_bijective_of_regular
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (h_compact : IsCompactObject
      ((derivedFunctor N).obj (DifferentialGradedModule.Derived.regularObject A)))
    (h_ext : (derivedFunctor N).IsFullyFaithfulOnSelfShifts
      (DifferentialGradedModule.Derived.regularObject A)) :
    ∀ X Y : DifferentialGradedModule.Derived.Category.{u, v} A,
      Function.Bijective
        ((derivedFunctor N).map :
          (X ⟶ Y) → ((derivedFunctor N).obj X ⟶ (derivedFunctor N).obj Y)) := sorry

/-- The compactness and self-extension assumptions of `09R9` imply bijectivity of derived
tensoring on every Hom set. -/
@[stacks 09R9 "Hom bijectivity from compact self-extensions"]
theorem map_bijective_of_compact_selfExt
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (h_compact : IsCompactObject N.rightDerivedObject)
    (h_selfExt : N.HasSelfExtComparison) :
    ∀ X Y : DifferentialGradedModule.Derived.Category.{u, v} A,
      Function.Bijective
        ((derivedFunctor N).map :
          (X ⟶ Y) → ((derivedFunctor N).obj X ⟶ (derivedFunctor N).obj Y)) := sorry

/-- Lemma 22.33.7 (09R9): if the right `B`-module represented by `N` is compact in `D(B)` and
the left `A`-action gives the expected self-extension isomorphisms in every degree, then
derived tensoring by `N` is fully faithful. -/
@[stacks 09R9]
noncomputable def fullyFaithful
    (N : DifferentialGradedBimodule.{u, v, v, v} A B)
    (h_compact : IsCompactObject N.rightDerivedObject)
    (h_selfExt : N.HasSelfExtComparison) :
    (derivedFunctor N).FullyFaithful :=
  Functor.FullyFaithful.ofMapBijective
    (map_bijective_of_compact_selfExt N h_compact h_selfExt)

end Tensor
end DifferentialGradedBimodule
