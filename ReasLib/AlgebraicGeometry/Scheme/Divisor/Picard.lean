/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.MeromorphicSection
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard
public import ReasLib.AlgebraicGeometry.Scheme.Normal
import Mathlib.Tactic.CrossRefAttribute

/-!
# The Picard group and the Weil divisor class group

For a locally Noetherian integral scheme, an invertible module determines a Weil divisor class.
This gives the comparison homomorphism from the Picard group to the Weil divisor class group. It is
injective on a normal scheme and is an isomorphism precisely in the locally factorial case.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- The canonical comparison homomorphism from the Picard group to the Weil divisor class group. -/
@[stacks 0BE7]
noncomputable def picardToWeilDivisorClassGroup :
    X.PicardGroup →+ Cl(X) :=
  AddMonoidHom.mk'
    (fun x ↦ @invertibleModuleWeilDivisorClass X _ _
      (PicardGroup.repr x) (by
        apply (isInvertibleObject.iff_exists_tensorInverse (PicardGroup.repr x)).2
        refine ⟨PicardGroup.repr (-x), ?_, ?_⟩
        · exact ⟨(PicardGroup.reprAddIso x (-x)).symm ≪≫
            eqToIso (congrArg PicardGroup.repr (add_neg_cancel x)) ≪≫
            PicardGroup.reprZeroIso⟩
        · exact ⟨(PicardGroup.reprAddIso (-x) x).symm ≪≫
            eqToIso (congrArg PicardGroup.repr (neg_add_cancel x)) ≪≫
            PicardGroup.reprZeroIso⟩))
    (by
      intro x y
      sorry)

/-- The comparison map can be computed using any nonzero meromorphic section of the canonical
representative of a Picard class. -/
theorem picardToWeilDivisorClassGroup_repr
    (x : X.PicardGroup)
    (s : X.toLocallyRingedSpace.meromorphicSections (PicardGroup.repr x))
    (hs : s ≠ 0) :
    picardToWeilDivisorClassGroup X x =
      nonzeroMeromorphicSectionWeilDivisorClass X
        (PicardGroup.repr x) s hs := sorry

/-- The comparison map can be computed using any nonzero meromorphic section of an explicit
invertible module. -/
theorem picardToWeilDivisorClassGroup_picardClass
    (ℒ : X.Modules) [Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : s ≠ 0) :
    picardToWeilDivisorClassGroup X (Modules.picardClass ℒ) =
      nonzeroMeromorphicSectionWeilDivisorClass X ℒ s hs := sorry

/-- On a normal scheme, the comparison map from the Picard group to the Weil divisor class group
is injective. -/
@[stacks 0BE8]
theorem injective_picardToWeilDivisorClassGroup (hX : X.isNormal) :
    Function.Injective (picardToWeilDivisorClassGroup X) := sorry

namespace PicardComparison

/-- Locally factorial schemes are normal and their Picard-to-class-group comparison is
surjective. -/
@[stacks 0BE9 "locally factorial implies normal and surjective"]
theorem normalAndSurjective
    (hUFD : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    X.isNormal ∧ Function.Surjective (picardToWeilDivisorClassGroup X) := sorry

/-- A normal scheme with surjective Picard-to-class-group comparison is locally factorial. -/
@[stacks 0BE9 "normal and surjective implies locally factorial"]
theorem locallyFactorial
    (hNormal : X.isNormal)
    (hsurj : Function.Surjective (picardToWeilDivisorClassGroup X)) :
    ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) := sorry

/-- On a locally factorial scheme, the Picard-to-class-group comparison is bijective. -/
@[stacks 0BE9 "comparison is an isomorphism"]
theorem bijective
    (hUFD : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    Function.Bijective (picardToWeilDivisorClassGroup X) := sorry

end PicardComparison

end AlgebraicGeometry.Scheme
