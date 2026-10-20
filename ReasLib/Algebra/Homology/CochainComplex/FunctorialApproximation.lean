/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Functorial Approximations of Cochain Complexes

This module owns the neutral data of a functorial cochain-complex approximation: an endofunctor
with a monomorphic, objectwise quasi-isomorphic comparison from the identity. It is independent
of any particular construction of the approximation, such as injective or acyclic-killing
replacements.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex

/-- A functorial cochain-complex approximation consists of an endofunctor together with an
objectwise monomorphic and quasi-isomorphic comparison from the identity functor. -/
@[stacks 079M "neutral functorial complex approximation"]
structure FunctorialComplexApproximation (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [CategoryWithHomology C] where
  /-- The underlying endofunctor on cochain complexes. -/
  toFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ
  /-- The natural comparison map from a complex to its chosen approximation. -/
  ι : 𝟭 (CochainComplex C ℤ) ⟶ toFunctor
  /-- Each comparison map is a monomorphism. -/
  mono_app (M : CochainComplex C ℤ) : Mono (ι.app M)
  /-- Each comparison map is a quasi-isomorphism. -/
  quasiIso_app (M : CochainComplex C ℤ) : QuasiIso (ι.app M)

namespace FunctorialComplexApproximation

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [CategoryWithHomology C]

/-- Construct a functorial cochain-complex approximation from its endofunctor,
comparison transformation, and componentwise properties. -/
def ofFunctor (F : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (comparison : 𝟭 (CochainComplex C ℤ) ⟶ F)
    (h_mono : ∀ complex, Mono (comparison.app complex))
    (h_quasiIso : ∀ complex, QuasiIso (comparison.app complex)) :
    FunctorialComplexApproximation C :=
  { toFunctor := F
    ι := comparison
    mono_app := h_mono
    quasiIso_app := h_quasiIso }

/-- The comparison components of `ofFunctor` are monomorphisms and quasi-isomorphisms. -/
theorem ofFunctor_spec (F : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (comparison : 𝟭 (CochainComplex C ℤ) ⟶ F)
    (h_mono : ∀ complex, Mono (comparison.app complex))
    (h_quasiIso : ∀ complex, QuasiIso (comparison.app complex))
    (complex : CochainComplex C ℤ) :
    Mono ((ofFunctor F comparison h_mono h_quasiIso).ι.app complex) ∧
      QuasiIso ((ofFunctor F comparison h_mono h_quasiIso).ι.app complex) := sorry

/-- The comparison natural transformation is monomorphic because all of its components are. -/
theorem mono_ι (J : FunctorialComplexApproximation C) : Mono J.ι :=
  { right_cancellation := fun g h eq => by
      apply NatTrans.ext
      apply funext
      intro M
      exact Mono.right_cancellation (self := J.mono_app M) _ _ (congr_app eq M) }

section FiniteLimits

variable [HasFiniteLimits C]

/-- Every degree of every comparison map in a functorial complex approximation is a
monomorphism. -/
theorem mono_f (J : FunctorialComplexApproximation C) (M : CochainComplex C ℤ) (n : ℤ) :
    Mono ((J.ι.app M).f n) := sorry

end FiniteLimits

end FunctorialComplexApproximation

end CochainComplex
