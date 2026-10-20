module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stalk.Nagata
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stalk.Quotient
public import ReasLib.RingTheory.AdicCompletion.AlgebraMap
public import ReasLib.RingTheory.Normalization.BaseChange.Henselian

@[expose] public section

/-!
# Completions of normalization stalks

This leaf names the local normalization completion constructions and obtains
their canonical maps from the general `AdicCompletion.extensionMap` API.
-/

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry TensorProduct nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Normalization.Stalk

variable (X : Scheme.{u})
variable [QuasiCompact (genericPointSpectrumCoproductTo X)]
variable [QuasiSeparated (genericPointSpectrumCoproductTo X)]

/-- The maximal-ideal completion of the local ring `𝒪_{X,x}`. -/
noncomputable abbrev completion (x : X) : Type u :=
  AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)

/-- The extension of the maximal ideal of `𝒪_{X,x}` to its canonical ring normalization. -/
noncomputable abbrev normalizationIdeal (x : X) :
    Ideal (Normalization.normalizationRing (X.presheaf.stalk x)) :=
  AdicCompletion.extensionIdeal (S := Normalization.normalizationRing (X.presheaf.stalk x))
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))

/-- The completion of the canonical ring normalization of `𝒪_{X,x}` along the extended maximal
ideal. -/
noncomputable abbrev normalizationCompletion (x : X) : Type u :=
  AdicCompletion (normalizationIdeal X x) (Normalization.normalizationRing (X.presheaf.stalk x))

/-- The extension of the maximal ideal of `𝒪_{X,x}` to `(ν_*𝒪_{X^ν})_x`. -/
noncomputable abbrev pushforwardIdeal (x : X) : Ideal (pushforward X x) :=
  AdicCompletion.extensionIdeal (S := pushforward X x)
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))

/-- The completion of `(ν_*𝒪_{X^ν})_x` along the ideal induced by the maximal ideal of
`𝒪_{X,x}`. -/
noncomputable abbrev pushforwardCompletion (x : X) : Type u :=
  AdicCompletion (pushforwardIdeal X x) (pushforward X x)

/-- The canonical map from the completion of `𝒪_{X,x}` to the completion of its ring
normalization. -/
noncomputable def completionToNormalization (x : X) :
    completion X x →+* normalizationCompletion X x :=
  AdicCompletion.extensionMap (S := Normalization.normalizationRing (X.presheaf.stalk x))
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))

namespace Completed.Ring

/-- The completed ring normalization is canonically an algebra over the completed source stalk. -/
noncomputable instance instAlgebra (x : X) :
    Algebra (completion X x) (normalizationCompletion X x) :=
  (completionToNormalization X x).toAlgebra

end Completed.Ring

/-- The canonical map from the completion of `𝒪_{X,x}` to the completion of
`(ν_*𝒪_{X^ν})_x`. -/
noncomputable def completionToPushforward (x : X) :
    completion X x →+* pushforwardCompletion X x :=
  AdicCompletion.extensionMap (S := pushforward X x)
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))

namespace Completed.Pushforward

/-- The completed normalization pushforward stalk is canonically an algebra over the completed
source stalk. -/
noncomputable instance instAlgebra (x : X) :
    Algebra (completion X x) (pushforwardCompletion X x) :=
  (completionToPushforward X x).toAlgebra

end Completed.Pushforward

/-- Evaluation of `completionToNormalization` at a finite quotient is its defining quotient map. -/
theorem eval_completionToNormalization (x : X) (n : ℕ) :
    (AdicCompletion.evalₐ (normalizationIdeal X x) n).toRingHom.comp
        (completionToNormalization X x) =
      AdicCompletion.extensionQuotientMap
        (S := Normalization.normalizationRing (X.presheaf.stalk x))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) n := sorry

/-- Evaluation of `completionToPushforward` at a finite quotient is its defining quotient map. -/
theorem eval_completionToPushforward (x : X) (n : ℕ) :
    (AdicCompletion.evalₐ (pushforwardIdeal X x) n).toRingHom.comp
        (completionToPushforward X x) =
      AdicCompletion.extensionQuotientMap (S := pushforward X x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) n := sorry

/-- The normalization completion map extends the canonical map from the source stalk to its ring
normalization. -/
theorem completionToNormalization_comp_algebraMap (x : X) :
    (completionToNormalization X x).comp
        (algebraMap (X.presheaf.stalk x) (completion X x)) =
      (algebraMap (Normalization.normalizationRing (X.presheaf.stalk x))
        (normalizationCompletion X x)).comp
        (algebraMap (X.presheaf.stalk x)
          (Normalization.normalizationRing (X.presheaf.stalk x))) := sorry

/-- The normalization-pushforward completion map extends the canonical map from the source stalk
to the normalization pushforward stalk. -/
theorem completionToPushforward_comp_algebraMap (x : X) :
    (completionToPushforward X x).comp
        (algebraMap (X.presheaf.stalk x) (completion X x)) =
      (algebraMap (pushforward X x) (pushforwardCompletion X x)).comp
        (pushforwardMap X x) := sorry

/-- The map from `𝒪_{X,x}` to the completion of its canonical ring normalization. -/
noncomputable def sourceToNormalizationCompletion (x : X) :
    X.presheaf.stalk x →+* normalizationCompletion X x :=
  (completionToNormalization X x).comp
    (algebraMap (X.presheaf.stalk x) (completion X x))

namespace Completed.Ring

/-- The completed ring normalization is canonically an algebra over the source stalk. -/
noncomputable instance instSourceAlgebra (x : X) :
    Algebra (X.presheaf.stalk x) (normalizationCompletion X x) :=
  (sourceToNormalizationCompletion X x).toAlgebra

/-- The source stalk, its completion, and its completed ring normalization form a canonical
scalar tower. -/
instance instScalarTower (x : X) :
    IsScalarTower (X.presheaf.stalk x) (completion X x) (normalizationCompletion X x) := sorry

end Completed.Ring

/-- The map from `𝒪_{X,x}` to the completion of `(ν_*𝒪_{X^ν})_x`. -/
noncomputable def sourceToPushforwardCompletion (x : X) :
    X.presheaf.stalk x →+* pushforwardCompletion X x :=
  (completionToPushforward X x).comp
    (algebraMap (X.presheaf.stalk x) (completion X x))

namespace Completed.Pushforward

/-- The canonical source-stalk algebra structure on the completed normalization pushforward
stalk. -/
noncomputable instance instSourceAlgebra (x : X) :
    Algebra (X.presheaf.stalk x) (pushforwardCompletion X x) :=
  (sourceToPushforwardCompletion X x).toAlgebra

/-- The source stalk, its completion, and the completed normalization pushforward stalk form a
canonical scalar tower. -/
instance instScalarTower (x : X) :
    IsScalarTower (X.presheaf.stalk x) (completion X x) (pushforwardCompletion X x) := sorry

end Completed.Pushforward

/-- The tensor product of the local ring normalization with its completed local ring. -/
noncomputable abbrev normalizationTensor (x : X) : Type u :=
  TensorProduct (X.presheaf.stalk x)
    (Normalization.normalizationRing (X.presheaf.stalk x)) (completion X x)

namespace Completed.Tensor

/-- The normalization tensor product is an algebra over the completed local ring through its
right tensor factor. -/
instance instRightAlgebra (x : X) :
    Algebra (completion X x) (normalizationTensor X x) :=
  Algebra.TensorProduct.rightAlgebra

end Completed.Tensor

/-- The quotient of the completed normalization pushforward stalk by the completed local ring. -/
noncomputable abbrev pushforwardCompletionQuotient (x : X) : Type u :=
  pushforwardCompletion X x ⧸
    (Algebra.linearMap (completion X x) (pushforwardCompletion X x)).range

/-- The quotient of the completed normalization pushforward stalk as a source-stalk module. -/
noncomputable abbrev pushforwardCompletionQuotientModule (x : X) :
    ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)) :=
  ModuleCat.of (RingCat.of (X.presheaf.stalk x)) (pushforwardCompletionQuotient X x)

variable [Nagata X]

namespace Completed.Tensor

/-- The normalization tensor product acts on the total quotient ring of the completed local ring. -/
instance instTotalQuotientAlgebra (x : X) :
    Algebra (normalizationTensor X x)
      (Localization (nonZeroDivisors (completion X x))) :=
  Normalization.BaseChange.Completion.algebra

end Completed.Tensor

end AlgebraicGeometry.Scheme.Normalization.Stalk
