/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Functoriality
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.Algebra.Homology.DerivedCategory.InjectiveAmplitude
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfectness criteria for derived internal-Hom comparisons

@stack 0ATK
@stack 0A68

This leaf collects the finiteness criteria used by the tensor-left and tensor-right comparison
maps.  It is a standard-universe module facade because the project `IsPerfect` and
`IsPseudoCoherent` predicates are owned at the canonical `ModuleCat` derived category.  The
comparison maps themselves still consume an explicit closed owner and fixed-right tensor model;
no selected structure is installed here.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped _root_.DerivedInternalHom

namespace CategoryTheory.DerivedCategory.InternalHom

variable {A : Type u} [CommRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]

namespace TensorLeft

/-- 15.99.3 (Stacks `0ATK`) (1): The tensor-left comparison is invertible when its
internal-Hom source is perfect. -/
@[stacks 0ATK "tensor-left comparison isomorphism for a perfect source"]
theorem comparisonOf_isIso_of_source_isPerfect
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L M : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)]
    (hM : M.IsPerfect) :
    IsIso (comparisonOf H T K L M) := sorry

/-- 15.99.3 (Stacks `0ATK`) (2): The tensor-left comparison is invertible when its tensor factor
is perfect. -/
@[stacks 0ATK "tensor-left comparison isomorphism for a perfect tensor factor"]
theorem comparisonOf_isIso_of_tensor_isPerfect
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L M : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)]
    (hK : K.IsPerfect) :
    IsIso (comparisonOf H T K L M) := sorry

/-- 15.99.3 (Stacks `0ATK`) (3): The tensor-left comparison is invertible under
pseudo-coherence, a lower bound, and a lower Tor-amplitude bound. -/
@[stacks 0ATK "tensor-left comparison isomorphism from Tor amplitude"]
theorem comparisonOf_isIso_of_isPseudoCoherent_of_boundedBelow_of_hasTorAmplitudeGE
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L M : DerivedCategory (ModuleCat.{u} A)) (a : ℤ)
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)]
    (hM : M.IsPseudoCoherent) (hL : ∃ n : ℤ, L.IsGE n)
    (hK : HasTorAmplitudeGE (R := A) K a) :
    IsIso (comparisonOf H T K L M) := sorry

/-- 15.99.3 (Stacks `0ATK`): The tensor-left comparison is invertible in any of its three
standard finiteness cases. -/
@[stacks 0ATK "tensor-left comparison isomorphism criterion"]
theorem comparisonOf_isIso_of_isPerfect_or_of_pseudoCoherent_boundedBelow_torAmplitudeGE
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L M : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)]
    (hcases : M.IsPerfect ∨ K.IsPerfect ∨
      ∃ a : ℤ, M.IsPseudoCoherent ∧ (∃ n : ℤ, L.IsGE n) ∧
        HasTorAmplitudeGE (R := A) K a) :
    IsIso (comparisonOf H T K L M) := by
  rcases hcases with hM | hK | ⟨a, hM, hL, hK⟩
  · exact comparisonOf_isIso_of_source_isPerfect H T K L M hM
  · exact comparisonOf_isIso_of_tensor_isPerfect H T K L M hK
  · exact
      comparisonOf_isIso_of_isPseudoCoherent_of_boundedBelow_of_hasTorAmplitudeGE
        H T K L M a hM hL hK

end TensorLeft

namespace TensorRight

/-- 15.99.1 (1): The tensor-right comparison is invertible when its tensor source is perfect. -/
@[stacks 0A68 "tensor-right comparison isomorphism for a perfect source"]
theorem comparisonOf_isIso_of_source_isPerfect
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L M : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)]
    (hK : K.IsPerfect) :
    IsIso (comparisonOf H T K L M) := sorry

/-- 15.99.1 (2): The tensor-right comparison is invertible under pseudo-coherence, a lower bound,
and finite injective dimension of its target. -/
@[stacks 0A68 "tensor-right comparison isomorphism from finite injective dimension"]
theorem comparisonOf_isIso_of_isPseudoCoherent_of_boundedBelow_of_finiteInjectiveDimension
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L M : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)]
    (hK : K.IsPseudoCoherent) (hL : ∃ n : ℤ, L.IsGE n)
    (hM : M.HasFiniteInjectiveDimension) :
    IsIso (comparisonOf H T K L M) := sorry

/-- 15.99.1: The tensor-right comparison is invertible in either standard finiteness case. -/
@[stacks 0A68 "tensor-right comparison isomorphism criterion"]
theorem comparisonOf_isIso_of_isPerfect_or_of_pseudoCoherent_boundedBelow_finiteInjectiveDimension
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L M : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)]
    (hcases : K.IsPerfect ∨
      K.IsPseudoCoherent ∧ (∃ n : ℤ, L.IsGE n) ∧ M.HasFiniteInjectiveDimension) :
    IsIso (comparisonOf H T K L M) := by
  rcases hcases with hK | ⟨hK, hL, hM⟩
  · exact comparisonOf_isIso_of_source_isPerfect H T K L M hK
  · exact
      comparisonOf_isIso_of_isPseudoCoherent_of_boundedBelow_of_finiteInjectiveDimension
        H T K L M hK hL hM

/-- 15.99.2: The tensor-right comparison is invertible when `L` and `M` have finite injective
dimension, `RHom[H](L, M)` has finite Tor dimension, and every standard lower truncation of `K`
is pseudo-coherent. -/
@[stacks 0A69 "tensor-right comparison isomorphism from truncation"]
theorem comparisonOf_isIso_of_finiteInjectiveDimension_of_finiteTorDimension_of_truncLE_isPseudoCoherent
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L M : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)]
    (hL : L.HasFiniteInjectiveDimension)
    (hM : M.HasFiniteInjectiveDimension)
    (hLM : HasFiniteTorDimension (R := A) (RHom[H](L, M)))
    (hK : ∀ n : ℤ,
      ((DerivedCategory.TStructure.t.truncLE n).obj K).IsPseudoCoherent) :
    IsIso (comparisonOf H T K L M) := sorry

end TensorRight

end CategoryTheory.DerivedCategory.InternalHom
