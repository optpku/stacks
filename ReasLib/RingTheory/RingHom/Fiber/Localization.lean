/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Principal localizations of residue-field fibers

This leaf owns the compatibility between taking a residue-field fiber and
localizing the target ring at one element.
-/

noncomputable section

universe u v

open scoped TensorProduct

namespace Ideal.Fiber

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The canonical right `S`-algebra structure on the residue-field fiber
`p.ResidueField ⊗[R] S`. -/
noncomputable instance rightAlgebra (p : Ideal R) [p.IsPrime] : Algebra S (p.Fiber S) :=
  Algebra.TensorProduct.rightAlgebra

/-- The right `S`-algebra structure on a residue-field fiber is compatible with its structural
`R`-algebra. -/
instance rightScalarTower (p : Ideal R) [p.IsPrime] : IsScalarTower R S (p.Fiber S) := sorry

namespace LocalizationAway

variable (p : Ideal R) [p.IsPrime] (g : S)

/-- The structural `R`- and `S`-algebras on a principal localization form the canonical scalar
tower. -/
instance targetScalarTower : IsScalarTower R S (Localization.Away g) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The tensor product used in the localization comparison carries the canonical right action of
the unlocalized fiber. -/
noncomputable instance tensorRightAlgebra :
    Algebra (p.Fiber S) (Localization.Away g ⊗[S] p.Fiber S) :=
  Algebra.TensorProduct.rightAlgebra

/-- Base change identifies the fiber of the localized target with the scalar extension of the
original fiber. -/
noncomputable def baseChange :
    p.Fiber (Localization.Away g) ≃ₐ[p.ResidueField]
      p.Fiber S ⊗[S] Localization.Away g :=
  (Algebra.IsPushout.cancelBaseChangeAlg R p.ResidueField S
    (p.Fiber S) (Localization.Away g)).symm

/-- Commuting the two tensor factors rewrites scalar extension as localization tensored on the
left. -/
noncomputable def commute :
    p.Fiber S ⊗[S] Localization.Away g ≃ₐ[p.Fiber S]
      Localization.Away g ⊗[S] p.Fiber S :=
  Algebra.TensorProduct.commRight S (p.Fiber S) (Localization.Away g)

/-- Tensoring a principal localization with the fiber gives localization of the fiber at the
image of the same element. -/
noncomputable def tensorRight :
    Localization.Away g ⊗[S] p.Fiber S ≃ₐ[p.Fiber S]
      Localization.Away ((Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) g) :=
  IsLocalization.Away.tensorRightEquiv (p.Fiber S) g (Localization.Away g)

/-- The ring equivalence underlying localization of a residue-field fiber. -/
noncomputable def ringEquiv :
    p.Fiber (Localization.Away g) ≃+*
      Localization.Away ((Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) g) :=
  (baseChange p g).toRingEquiv.trans (commute p g).toRingEquiv |>.trans
    (tensorRight p g).toRingEquiv

/-- The localization ring equivalence preserves the residue-field algebra map. -/
theorem ringEquiv_commutes (x : p.ResidueField) :
    ringEquiv p g (algebraMap p.ResidueField (p.Fiber (Localization.Away g)) x) =
      algebraMap p.ResidueField
        (Localization.Away ((Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) g)) x :=
  sorry

end LocalizationAway

/-- The residue-field fiber over `p` of the principal localization `S_g` is canonically the
principal localization of the fiber `p.Fiber S` away from the image of `g`.

This is an equivalence of `p.ResidueField`-algebras; the target action is through the canonical
right tensor map from `S` to `p.Fiber S`. -/
@[stacks 00SO "fiber localization commutes with principal localization"]
noncomputable def localizationAwayAlgEquiv (p : Ideal R) [p.IsPrime] (g : S) :
    p.Fiber (Localization.Away g) ≃ₐ[p.ResidueField]
      Localization.Away ((Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) g) where
  toRingEquiv := LocalizationAway.ringEquiv p g
  commutes' := LocalizationAway.ringEquiv_commutes p g

/-- The forward fiber-localization equivalence is the composite of base change, tensor symmetry,
and tensor localization. -/
@[simp]
theorem localizationAwayAlgEquiv_apply (p : Ideal R) [p.IsPrime] (g : S)
    (x : p.Fiber (Localization.Away g)) :
    localizationAwayAlgEquiv p g x =
      LocalizationAway.tensorRight p g
        (LocalizationAway.commute p g (LocalizationAway.baseChange p g x)) := sorry

/-- The inverse fiber-localization equivalence applies the three canonical inverse comparisons in
reverse order. -/
@[simp]
theorem localizationAwayAlgEquiv_symm_apply (p : Ideal R) [p.IsPrime] (g : S)
    (x : Localization.Away
      ((Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) g)) :
    (localizationAwayAlgEquiv p g).symm x =
      (LocalizationAway.baseChange p g).symm
        ((LocalizationAway.commute p g).symm
          ((LocalizationAway.tensorRight p g).symm x)) := sorry

section InstanceChecks

variable (p : Ideal R) [p.IsPrime] (g : S)

#synth Algebra S (p.Fiber S)
#synth IsScalarTower R S (p.Fiber S)
#synth IsScalarTower R S (Localization.Away g)
#synth Algebra (p.Fiber S) (Localization.Away g ⊗[S] p.Fiber S)

end InstanceChecks

end Ideal.Fiber
