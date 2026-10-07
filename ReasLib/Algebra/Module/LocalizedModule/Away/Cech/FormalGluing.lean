module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# The Formal-Gluing Cech Complex

This leaf owns the explicit two maps in the module formal-gluing complex.  The first map combines
extension of scalars with the principal-open family map; the second records compatibility both
after extension of scalars and on pairwise principal-open overlaps.

@stack 05EJ
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u v

namespace LocalizedModule.Away.Cech.FormalGluing

local notation "Away" => LocalizedModule.Away

/-- Local instance justification (defeq pin): keep the scalar structure used by `LinearMap`
aligned with the ring structure consumed by `ShortComplex.moduleCatMk`. -/
local instance (priority := 10000) ringSemiringOfCommRing
    {A : Type u} [CommRing A] : Semiring A :=
  (inferInstance : Ring A).toSemiring

variable {R : Type u} [CommRing R]
variable {ι : Type v}

/-- The middle module in the formal-gluing Cech complex. -/
@[stacks 05EJ "formal-gluing Cech middle module"]
abbrev Middle (S : Type u) [CommRing S] [Algebra R S]
    (f : ι → R) (M : ModuleCat.{max u v} R) : Type (max u v) :=
  (S ⊗[R] M) × ((i : ι) → Away (f i) M)

/-- The target module in the formal-gluing Cech complex. -/
@[stacks 05EJ "formal-gluing Cech target module"]
abbrev Target (S : Type u) [CommRing S] [Algebra R S]
    (f : ι → R) (M : ModuleCat.{max u v} R) : Type (max u v) :=
  ((i : ι) → Away (f i) (S ⊗[R] M)) ×
    ((i : ι) → (j : ι) → Away (f i * f j) M)

/-- Equation 15.90.8.1: the first map in the formal-gluing Cech complex. -/
@[stacks 05EJ "formal-gluing Cech first map"]
noncomputable def alpha
    (S : Type u) [CommRing S] [Algebra R S]
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    M →ₗ[R] Middle S f M :=
  (TensorProduct.mk R S M 1).prod (LocalizedModule.Away.Cech.familyMap M f)

/-- The scalar-extension component of the second formal-gluing Cech map. -/
@[stacks 05EJ "formal-gluing Cech scalar-extension component"]
noncomputable def betaTensor
    (S : Type u) [CommRing S] [Algebra R S]
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    Middle S f M →ₗ[R] ((i : ι) → Away (f i) (S ⊗[R] M)) :=
  -- Local instance justification (defeq pin): use the group-derived additive monoid for the
  -- tensor product throughout the two localization maps.
  letI : AddCommGroup (S ⊗[R] (M : Type (max u v))) := inferInstance
  -- Local instance justification (defeq pin): align the tensor-product additive monoid with the
  -- preceding additive-group choice.
  letI : AddCommMonoid (S ⊗[R] (M : Type (max u v))) :=
    (inferInstance : AddCommGroup (S ⊗[R] (M : Type (max u v)))).toAddCommMonoid
  -- Local instance justification (defeq pin): build the scalar action from the aligned additive
  -- structure used by principal-open localization.
  letI : Module R (S ⊗[R] (M : Type (max u v))) := inferInstance
  (LocalizedModule.Away.Cech.familyMap (S ⊗[R] M) f).comp
      (LinearMap.fst R (S ⊗[R] M) ((i : ι) → Away (f i) M)) -
    (LocalizedModule.Away.Cech.mapFamily f (TensorProduct.mk R S M 1)).comp
      (LinearMap.snd R (S ⊗[R] M) ((i : ι) → Away (f i) M))

/-- The pairwise-overlap component of the second formal-gluing Cech map. -/
@[stacks 05EJ "formal-gluing Cech overlap component"]
noncomputable def betaOverlap
    (S : Type u) [CommRing S] [Algebra R S]
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    Middle S f M →ₗ[R] ((i : ι) → (j : ι) → Away (f i * f j) M) :=
  (LocalizedModule.Away.Cech.compatibilityMap M f).comp
    (LinearMap.snd R (S ⊗[R] M) ((i : ι) → Away (f i) M))

/-- Equation 15.90.8.1: the second map in the formal-gluing Cech complex. -/
@[stacks 05EJ "formal-gluing Cech second map"]
noncomputable def beta
    (S : Type u) [CommRing S] [Algebra R S]
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    Middle S f M →ₗ[R] Target S f M :=
  LinearMap.prod (betaTensor S f M) (betaOverlap S f M)

/-- Consecutive maps in the formal-gluing Cech complex have zero composite. -/
@[stacks 05EJ "formal-gluing Cech complex"]
theorem comp_eq_zero
    (S : Type u) [CommRing S] [Algebra R S]
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    (beta S f M).comp (alpha S f M) = 0 := sorry

/-- Equation 15.90.8.1: the formal-gluing module sequence as a short complex. -/
@[stacks 05EJ "formal-gluing Cech short complex"]
noncomputable def complex
    (S : Type u) [CommRing S] [Algebra R S]
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    ShortComplex (ModuleCat.{max u v} R) :=
  let X₂ : Type (max u v) := Middle S f M
  let X₃ : Type (max u v) := Target S f M
  let middleGroup : AddCommGroup X₂ := inferInstance
  let targetGroup : AddCommGroup X₃ := inferInstance
  -- Local instance justification (defeq pin): `moduleCatMk` must use the same additive monoid as
  -- the explicit middle linear map.
  letI : AddCommGroup X₂ :=
    { middleGroup with toAddCommMonoid := (inferInstance : AddCommMonoid X₂) }
  -- Local instance justification (defeq pin): align the target object with the additive monoid
  -- already present in the explicit second linear map.
  letI : AddCommGroup X₃ :=
    { targetGroup with toAddCommMonoid := (inferInstance : AddCommMonoid X₃) }
  ShortComplex.moduleCatMk (alpha S f M) (beta S f M) (comp_eq_zero S f M)

end LocalizedModule.Away.Cech.FormalGluing
