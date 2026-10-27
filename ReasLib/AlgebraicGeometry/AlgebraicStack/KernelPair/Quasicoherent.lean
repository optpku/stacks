/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.KernelPair.Fppf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.LocalEquivalence.Extension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Quotient

/-!
# Quasi-coherent modules on flat kernel-pair presentations

A surjective flat locally finitely presented morphism from an algebraic space
presents quasi-coherent modules on an algebraic stack as equivariant modules
on its kernel-pair groupoid. Reconstruction uses compatible-section extension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
variable (U : AlgebraicSpace S) (f : U.toGroupoids ⟶ X)
variable [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
variable [Groupoids.Hom.LocallyOfFinitePresentation f]

/-- Pullback along the canonical kernel-pair quotient map is an equivalence,
with inverse given by compatible-section extension. -/
def qCohFCanEquivalence :
    GroupoidsOver.QCoh X ≌
      GroupoidsOver.QCoh
        (GroupoidAlgebraicSpace.SmallQuotient.quotientStack
          (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U))) :=
  GroupoidsOver.LocalEquivalenceModules.qcohEquivalence
    (fCan f (IsRepresentableByAlgebraicSpace.of_toGroupoids U))
    (FiberedCategoryOver.Hom.IsLocalEquivalence.of_isEquivalence
      (Scheme.fppfTopology.over S)
      ((FiberedCategoryOver.Groupoids.toFibered (Over S)).map
        (fCan f (IsRepresentableByAlgebraicSpace.of_toGroupoids U)))
      (fCan_isEquivalence_of_flat f
        (IsRepresentableByAlgebraicSpace.of_toGroupoids U)))

/-- Pullback of quasi-coherent modules along the canonical quotient map of a
surjective flat locally finitely presented atlas is an equivalence. -/
instance qCohPullback_fCan_isEquivalence :
    (GroupoidsOver.QCoh.pullback
      (fCan f (IsRepresentableByAlgebraicSpace.of_toGroupoids U))).IsEquivalence :=
  (qCohFCanEquivalence U f).isEquivalence_functor

/-- Quasi-coherent modules on an algebraic stack are equivalent to equivariant
quasi-coherent modules on the kernel-pair groupoid of a surjective flat locally
finitely presented atlas. -/
def qCohEquivalence :
    GroupoidsOver.QCoh X ≌
      (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U)).QCoh :=
  (qCohFCanEquivalence U f).trans
    (GroupoidsOver.QCoh.toGroupoidEquivalence
      (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U)))

/-- The forward functor of `qCohEquivalence` is pullback along `fCan` followed by
`toGroupoid`. -/
theorem qCohEquivalence_functor :
    (qCohEquivalence U f).functor =
      GroupoidsOver.QCoh.pullback
          (fCan f (IsRepresentableByAlgebraicSpace.of_toGroupoids U)) ⋙
        GroupoidsOver.QCoh.toGroupoid
          (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U)) :=
  sorry

/-- The inverse functor of `qCohEquivalence` is `fromGroupoid` followed by the
compatible-section extension along `fCan`. -/
theorem qCohEquivalence_inverse :
    (qCohEquivalence U f).inverse =
      (GroupoidsOver.QCoh.toGroupoidEquivalence
            (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U))).inverse ⋙
        (qCohFCanEquivalence U f).inverse :=
  sorry

end AlgebraicGeometry.AlgebraicStack
