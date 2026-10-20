module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.RingTheory.Extension.Cotangent.LocalizationAway
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Canonical

/-!
# Localization away for naive cotangent complexes

This leaf owns the presentation-level comparison from the literal scalar
extension of a naive cotangent complex to the canonical naive cotangent
complex after localizing away from one element.  Its explicit tensor model is
kept as a normalized implementation layer.  The local tensor-product
instances fix the same ambient scalar structure as `BaseChange`; they remain
local to avoid global instance diamonds.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped NaiveCotangent TensorProduct Algebra.TensorProduct.Right

universe u v

noncomputable section

namespace Algebra.Extension.NaiveCotangent.LocalizationAway

variable {R : Type u} {S T : Type v}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable {ι : Type v}

-- Local instance justification (instance diamond): the tensor-model maps use the same fixed
-- `Algebra.TensorProduct.Right` interpretation as `BaseChange`; this auxiliary commutation fact
-- must stay local to avoid a global competing scalar structure.
attribute [local instance] SMulCommClass.of_commMonoid

/-- The canonical away-localization presentation, reindexed into the ambient generator universe.
This explicit reindexing keeps composable presentations in one `ModuleCat` universe. -/
noncomputable def localizationGenerators (g : S) [IsLocalization.Away g T] :
    Algebra.Generators S T (ULift.{v} Unit) :=
  (Algebra.Generators.localizationAway (R := S) (S := T) g).reindex Equiv.ulift

/-- The tensor-model map to the presentation obtained by adjoining an inverse of `g`. -/
@[stacks 08JZ "localized presentation map"]
noncomputable def toLocalizedPresentation
    (P : Algebra.Generators R S ι) (g : S) [IsLocalization.Away g T] :
    BaseChange.tensorModel (T := T) P.toExtension ⟶
      complex ((localizationGenerators (S := S) (T := T) g).comp P).toExtension :=
  BaseChange.toComp (R := R) (S := S) (T := T) P
    (localizationGenerators (S := S) (T := T) g)

/-- Presentation independence identifies the localized presentation with the self-presentation
of its target algebra. -/
@[stacks 08JZ "localized presentation normalization"]
noncomputable def localizedPresentationHomotopyEquiv
    (P : Algebra.Generators R S ι) (g : S) [IsLocalization.Away g T] :
    HomotopyEquiv
      (complex ((localizationGenerators (S := S) (T := T) g).comp P).toExtension)
      (complex (Algebra.Generators.self R T).toExtension) :=
  generatorsHomotopyEquiv (R := R) (S := T)
    ((localizationGenerators (S := S) (T := T) g).comp P)
    (Algebra.Generators.self R T)

/-- The normalized localization-away comparison from the tensor model of a presentation to the
canonical naive cotangent complex of the localized target. -/
@[stacks 08JZ "tensor-model localization comparison"]
noncomputable def modelComparison
    (P : Algebra.Generators R S ι) (g : S) [IsLocalization.Away g T] :
    BaseChange.tensorModel (T := T) P.toExtension ⟶
      complex (Algebra.Generators.self R T).toExtension :=
  toLocalizedPresentation (R := R) (S := S) (T := T) P g ≫
    (localizedPresentationHomotopyEquiv (R := R) (S := S) (T := T) P g).hom

/-- The normalized localization-away comparison becomes an isomorphism in the homotopy category. -/
theorem modelComparison_isIso
    (P : Algebra.Generators R S ι) (g : S) [IsLocalization.Away g T] :
    IsIso
      ((HomotopyCategory.quotient (ModuleCat T) (ComplexShape.down ℕ)).map
        (modelComparison P g)) := sorry

/-- The localization-away comparison from literal scalar extension to the canonical naive
cotangent complex of the localized target. -/
@[stacks 08JZ "literal scalar-extension localization comparison"]
noncomputable def comparison
    (P : Algebra.Generators R S ι) (g : S) [IsLocalization.Away g T] :
    BaseChange.scalarExtension (T := T) P.toExtension ⟶
      complex (Algebra.Generators.self R T).toExtension :=
  (BaseChange.scalarExtensionIsoTensorModel (R := R) (S := S) (T := T) P.toExtension).hom ≫
    modelComparison (R := R) (S := S) (T := T) P g

/-- The literal scalar-extension localization-away comparison becomes an isomorphism in the
homotopy category. -/
theorem comparison_isIso
    (P : Algebra.Generators R S ι) (g : S) [IsLocalization.Away g T] :
    IsIso
      ((HomotopyCategory.quotient (ModuleCat T) (ComplexShape.down ℕ)).map
        (comparison P g)) := sorry

end Algebra.Extension.NaiveCotangent.LocalizationAway

namespace Algebra.NaiveCotangent.LocalizationAway

variable {R : Type u} {S T : Type v}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- The canonical localization-away comparison for the self-presentation of an algebra.  Its
source is the literal scalar extension of `NL{S⁄R}` from `S` to `T`. -/
@[stacks 08JZ "canonical literal scalar-extension comparison"]
noncomputable def comparison (g : S) [IsLocalization.Away g T] :
    Extension.NaiveCotangent.BaseChange.scalarExtension (T := T)
      (Algebra.Generators.self R S).toExtension ⟶
      NL{T⁄R} :=
  Extension.NaiveCotangent.LocalizationAway.comparison (R := R) (S := S) (T := T)
    (Algebra.Generators.self R S) g

/-- Lemma 10.134.12, tag `08JZ`: the canonical localization-away comparison becomes an
isomorphism in the homotopy category. -/
@[stacks 08JZ]
theorem comparison_isIso (g : S) [IsLocalization.Away g T] :
    IsIso
      ((HomotopyCategory.quotient (ModuleCat T) (ComplexShape.down ℕ)).map
        (comparison (R := R) (S := S) (T := T) g)) := sorry

end Algebra.NaiveCotangent.LocalizationAway
