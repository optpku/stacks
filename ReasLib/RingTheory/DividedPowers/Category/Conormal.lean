module

public import ReasLib.RingTheory.DividedPowers.SecondOrder
public import ReasLib.RingTheory.DividedPowers.Category
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open DividedPowers

universe u

noncomputable section

namespace DividedPowerRing.Pushout

/-- The canonical fold map from a divided-power self-pushout to its common factor. -/
def fold {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) : B₁ ⟶ B :=
  hpush.desc (𝟙 B) (𝟙 B) (by simp)

/-- The fold restricts to the identity on the left coprojection. -/
theorem fold_fac_left {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) : s₀ ≫ fold f s₀ s₁ hpush = 𝟙 B := sorry

/-- The fold restricts to the identity on the right coprojection. -/
theorem fold_fac_right {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) : s₁ ≫ fold f s₀ s₁ hpush = 𝟙 B := sorry

/-- The kernel quotient by the ordinary square and the second-order divided-power ideal,
viewed as a module over the left copy of `B`. -/
abbrev kernelQuotient {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) : Type u :=
  -- Local instance justification (instance diamond): the left coprojection selects the `B`-algebra structure on `B₁`.
  letI : Algebra B B₁ := s₀.toRingHom.toAlgebra
  let K := RingHom.ker (fold f s₀ s₁ hpush).toRingHom
  let L := K ^ 2 ⊔ B₁.dividedPowers.secondOrderIdeal K
  (K.restrictScalars B) ⧸ (L.restrictScalars B).comap (K.restrictScalars B).subtype

/-- The kernel quotient is the indicated restricted-scalar submodule quotient. -/
theorem kernelQuotient_def {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) :
    kernelQuotient f s₀ s₁ hpush =
      -- Local instance justification (instance diamond): the left coprojection selects the `B`-algebra structure on `B₁`.
      letI : Algebra B B₁ := s₀.toRingHom.toAlgebra
      let K := RingHom.ker (fold f s₀ s₁ hpush).toRingHom
      let L := K ^ 2 ⊔ B₁.dividedPowers.secondOrderIdeal K
      (K.restrictScalars B) ⧸ (L.restrictScalars B).comap (K.restrictScalars B).subtype := sorry

/-- The fold kernel intersected with the distinguished ideal is stable under divided powers. -/
theorem isSubDPIdeal_kernel {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) :
    DividedPowers.IsSubDPIdeal B₁.dividedPowers
      (RingHom.ker (fold f s₀ s₁ hpush).toRingHom ⊓ B₁.ideal) := sorry

/-- The relations used in the kernel quotient are contained in the fold kernel. -/
theorem kernelRelations_le {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) :
    (RingHom.ker (fold f s₀ s₁ hpush).toRingHom) ^ 2 ⊔
        B₁.dividedPowers.secondOrderIdeal (RingHom.ker (fold f s₀ s₁ hpush).toRingHom) ≤
      RingHom.ker (fold f s₀ s₁ hpush).toRingHom := sorry

/-- The difference of the two coprojections lies in the kernel of the fold. -/
theorem kernelDifference_mem {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) (b : B) :
    s₁.toRingHom b - s₀.toRingHom b ∈ RingHom.ker (fold f s₀ s₁ hpush).toRingHom := sorry

set_option backward.privateInPublic true in
/-- The quotient class of the difference between the two coprojections. -/
private def differenceClass {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) (b : B) : kernelQuotient f s₀ s₁ hpush :=
  Submodule.Quotient.mk
    ⟨s₁.toRingHom b - s₀.toRingHom b, kernelDifference_mem f s₀ s₁ hpush b⟩

set_option backward.privateInPublic true in
/-- The difference class is additive. -/
private theorem differenceClass_add {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) (b₀ b₁ : B) :
    differenceClass f s₀ s₁ hpush (b₀ + b₁) =
      differenceClass f s₀ s₁ hpush b₀ + differenceClass f s₀ s₁ hpush b₁ := sorry

set_option backward.privateInPublic true in
/-- The difference class respects the scalar action selected by the source morphism. -/
private theorem differenceClass_smul {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) (a : A) (b : B) :
    -- Local instance justification (noncanonical choice): the morphism `f` selects one of the possible `A`-algebra structures on `B`.
    letI : Algebra A B := f.toRingHom.toAlgebra
    -- Local instance justification (defeq pin): the quotient's `A`-action must be restriction of its fixed left-copy `B`-action along `f`.
    letI : Module A (kernelQuotient f s₀ s₁ hpush) := Module.compHom _ f.toRingHom
    differenceClass f s₀ s₁ hpush (a • b) = a • differenceClass f s₀ s₁ hpush b := sorry

set_option backward.privateInPublic true in
/-- The source-linear first-order difference map into the kernel quotient. -/
def kernelDifference {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) :
    -- Local instance justification (noncanonical choice): the morphism `f` selects one of the possible `A`-algebra structures on `B`.
    letI : Algebra A B := f.toRingHom.toAlgebra
    -- Local instance justification (defeq pin): the quotient's `A`-action must be restriction of its fixed left-copy `B`-action along `f`.
    letI : Module A (kernelQuotient f s₀ s₁ hpush) := Module.compHom _ f.toRingHom
    B →ₗ[A] kernelQuotient f s₀ s₁ hpush :=
  -- Local instance justification (noncanonical choice): the morphism `f` selects one of the possible `A`-algebra structures on `B`.
  letI : Algebra A B := f.toRingHom.toAlgebra
  -- Local instance justification (defeq pin): the quotient's `A`-action must be restriction of its fixed left-copy `B`-action along `f`.
  letI : Module A (kernelQuotient f s₀ s₁ hpush) := Module.compHom _ f.toRingHom
  { toFun := differenceClass f s₀ s₁ hpush
    map_add' := differenceClass_add f s₀ s₁ hpush
    map_smul' := differenceClass_smul f s₀ s₁ hpush }

/-- The first-order difference map is represented by the difference of the coprojections. -/
theorem kernelDifference_apply {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) (b : B) :
    kernelDifference f s₀ s₁ hpush b =
      Submodule.Quotient.mk ⟨s₁.toRingHom b - s₀.toRingHom b,
        kernelDifference_mem f s₀ s₁ hpush b⟩ := sorry

set_option backward.privateInPublic true in
/-- The first-order difference map vanishes on the unit. -/
private theorem kernelDifference_one {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) : kernelDifference f s₀ s₁ hpush 1 = 0 := sorry

set_option backward.privateInPublic true in
/-- The first-order difference map satisfies the Leibniz rule for the left-copy action. -/
private theorem kernelDifference_leibniz {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) (a b : B) :
    kernelDifference f s₀ s₁ hpush (a * b) =
      a • kernelDifference f s₀ s₁ hpush b + b • kernelDifference f s₀ s₁ hpush a := sorry

set_option backward.privateInPublic true in
/-- The derivation obtained from the difference of the two coprojections. -/
def kernelDerivation {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) :
    -- Local instance justification (noncanonical choice): the morphism `f` selects one of the possible `A`-algebra structures on `B`.
    letI : Algebra A B := f.toRingHom.toAlgebra
    -- Local instance justification (defeq pin): the quotient's `A`-action must be restriction of its fixed left-copy `B`-action along `f`.
    letI : Module A (kernelQuotient f s₀ s₁ hpush) := Module.compHom _ f.toRingHom
    Derivation A B (kernelQuotient f s₀ s₁ hpush) :=
  -- Local instance justification (noncanonical choice): the morphism `f` selects one of the possible `A`-algebra structures on `B`.
  letI : Algebra A B := f.toRingHom.toAlgebra
  -- Local instance justification (defeq pin): the quotient's `A`-action must be restriction of its fixed left-copy `B`-action along `f`.
  letI : Module A (kernelQuotient f s₀ s₁ hpush) := Module.compHom _ f.toRingHom
  { toLinearMap := kernelDifference f s₀ s₁ hpush
    map_one_eq_zero' := kernelDifference_one f s₀ s₁ hpush
    leibniz' := kernelDifference_leibniz f s₀ s₁ hpush }

/-- The kernel derivation has the same underlying function as the first-order difference map. -/
theorem kernelDerivation_apply {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) (b : B) :
    kernelDerivation f s₀ s₁ hpush b = kernelDifference f s₀ s₁ hpush b := sorry

set_option backward.privateInPublic true in
/-- The lifted kernel derivation annihilates the divided-power differential relations. -/
private theorem kernelDerivation_relations_le {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B)
    (s₀ s₁ : B ⟶ B₁) (hpush : IsPushout f f s₀ s₁) :
    -- Local instance justification (noncanonical choice): the morphism `f` selects the `A`-algebra structure required by Kähler differentials.
    letI : Algebra A B := f.toRingHom.toAlgebra
    -- Local instance justification (defeq pin): the restricted quotient action must coincide with the action in the kernel derivation.
    letI : Module A (kernelQuotient f s₀ s₁ hpush) := Module.compHom _ f.toRingHom
    -- Local instance justification (defeq pin): `liftKaehlerDifferential` requires the scalar tower for this morphism-selected restricted action.
    letI : IsScalarTower A B (kernelQuotient f s₀ s₁ hpush) := IsScalarTower.of_compHom A B _
    KaehlerDifferential.DeRham.dividedPowerRelations f.toRingHom B.dividedPowers ≤
      LinearMap.ker (kernelDerivation f s₀ s₁ hpush).liftKaehlerDifferential := sorry

set_option backward.privateInPublic true in
/-- The canonical comparison map from divided-power differentials to the kernel quotient. -/
def kernelComparison {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) :
    KaehlerDifferential.DeRham.dividedPowerDifferential f.toRingHom B.dividedPowers →ₗ[B]
      kernelQuotient f s₀ s₁ hpush :=
  -- Local instance justification (noncanonical choice): the morphism `f` selects the `A`-algebra structure required by Kähler differentials.
  letI : Algebra A B := f.toRingHom.toAlgebra
  -- Local instance justification (defeq pin): the restricted quotient action must coincide with the action in the kernel derivation.
  letI : Module A (kernelQuotient f s₀ s₁ hpush) := Module.compHom _ f.toRingHom
  -- Local instance justification (defeq pin): `liftKaehlerDifferential` requires the scalar tower for this morphism-selected restricted action.
  letI : IsScalarTower A B (kernelQuotient f s₀ s₁ hpush) := IsScalarTower.of_compHom A B _
  (KaehlerDifferential.DeRham.dividedPowerRelations f.toRingHom B.dividedPowers).liftQ
    (kernelDerivation f s₀ s₁ hpush).liftKaehlerDifferential
    (kernelDerivation_relations_le f s₀ s₁ hpush)

/-- The comparison sends the universal divided-power differential of `b` to its difference class. -/
theorem kernelComparison_apply {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) (b : B) :
    kernelComparison f s₀ s₁ hpush
        (KaehlerDifferential.DeRham.dividedPowerDifferentialDerivation
          f.toRingHom B.dividedPowers b) = kernelDifference f s₀ s₁ hpush b := sorry

/-- The canonical comparison from divided-power differentials to the fold-kernel quotient is bijective. -/
theorem kernelComparison_bijective {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B) (s₀ s₁ : B ⟶ B₁)
    (hpush : IsPushout f f s₀ s₁) : Function.Bijective (kernelComparison f s₀ s₁ hpush) := sorry

/-- The canonical linear equivalence from divided-power differentials to the conormal
quotient of a divided-power self-pushout. -/
noncomputable def kernelComparisonEquiv {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B)
    (s₀ s₁ : B ⟶ B₁) (hpush : IsPushout f f s₀ s₁) :
    KaehlerDifferential.DeRham.dividedPowerDifferential f.toRingHom B.dividedPowers ≃ₗ[B]
      kernelQuotient f s₀ s₁ hpush :=
  LinearEquiv.ofBijective
    (kernelComparison f s₀ s₁ hpush)
    (kernelComparison_bijective f s₀ s₁ hpush)

/-- The canonical equivalence sends the universal divided-power differential of `b` to its
first-order difference class in the conormal quotient. -/
theorem kernelComparisonEquiv_apply {A B B₁ : DividedPowerRing.{u}} (f : A ⟶ B)
    (s₀ s₁ : B ⟶ B₁) (hpush : IsPushout f f s₀ s₁) (b : B) :
    kernelComparisonEquiv f s₀ s₁ hpush
        (KaehlerDifferential.DeRham.dividedPowerDifferentialDerivation
          f.toRingHom B.dividedPowers b) =
      kernelDifference f s₀ s₁ hpush b := sorry

end DividedPowerRing.Pushout

end
