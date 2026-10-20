/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PolynomialTower.Differentials
public import stacks_project.Chap92.Lemma_92_7_1_Omega
public import stacks_project.Chap92.«92_7_0_2_Triple»

/-!
# Compatibility with polynomial triples

The differential sequence on legacy polynomial triples is obtained by precomposing
with the functor to commutative polynomial squares.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false

namespace RingedSite.Cotangent.PolynomialTriple

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

variable {A B C}

private abbrev qAsA (X : PolynomialTriple A B C) : CommAlgCat A :=
  @CommAlgCat.of A _ X.Q _ (algebraAQ X)

private def pqMap (X : PolynomialTriple A B C) : CommAlgCat.of A X.P ⟶ qAsA X :=
  @CommAlgCat.ofHom A _ X.P X.Q _ _ _ (algebraAQ X)
    (@AlgHom.mk A X.P X.Q _ _ _ _ (algebraAQ X) (algebraMap X.P X.Q) (fun _ ↦ rfl))

private def qcMap (X : PolynomialTriple A B C) : qAsA X ⟶ CommAlgCat.of A C :=
  @CommAlgCat.ofHom A _ X.Q C _ (algebraAQ X) _ _
    (@AlgHom.mk A X.Q C _ _ _ (algebraAQ X) _ (toCRingHom X) (fun a ↦ by
        change X.toC (algebraMap X.P X.Q (algebraMap A X.P a)) = algebraMap A C a
        rw [@AlgHom.commutes X.P X.Q C _ _ _ X.algebraPQ (algebraPCOf X.toB) X.toC]
        change algebraMap B C (X.toB (algebraMap A X.P a)) = algebraMap A C a
        rw [X.toB.commutes, ← IsScalarTower.algebraMap_apply]))

private def towerObj (X : PolynomialTriple A B C) : Algebra.PolynomialTower A B C :=
  Algebra.PolynomialTower.ofSquare (pqMap X) (CommAlgCat.ofHom X.toB) (qcMap X)
    (by
      ext p
      exact (@AlgHom.commutes X.P X.Q C _ _ _ X.algebraPQ (algebraPCOf X.toB)
        X.toC p).symm)
    X.isPolynomialP
    (by
      change @Algebra.IsPolynomial X.P X.Q _ _ (algebraMap X.P X.Q).toAlgebra
      rw [toAlgebra_algebraMap]
      exact X.isPolynomialQ)

private def qMap {X Y : PolynomialTriple A B C} (f : X ⟶ Y) : qAsA X ⟶ qAsA Y :=
  @CommAlgCat.ofHom A _ X.Q Y.Q _ (algebraAQ X) _ (algebraAQ Y)
    (@AlgHom.mk A X.Q Y.Q _ _ _ (algebraAQ X) (algebraAQ Y) f.toQ (fun a ↦ by
        change f.toQ (algebraMap X.P X.Q (algebraMap A X.P a)) =
          algebraMap Y.P Y.Q (algebraMap A Y.P a)
        have h := RingHom.congr_fun f.commP (algebraMap A X.P a)
        change f.toQ (algebraMap X.P X.Q (algebraMap A X.P a)) =
          algebraMap Y.P Y.Q (f.toP (algebraMap A X.P a)) at h
        rw [h, f.toP.commutes]))

private def towerMap {X Y : PolynomialTriple A B C} (f : X ⟶ Y) : towerObj X ⟶ towerObj Y :=
  ObjectProperty.homMk (Over.homMk
    (Arrow.homMk (CommAlgCat.ofHom f.toP) (qMap f)
      (by ext p; exact (RingHom.congr_fun f.commP p).symm))
    (by
      apply Arrow.hom_ext
      · ext p
        exact AlgHom.congr_fun f.commB p
      · ext q
        exact RingHom.congr_fun f.commC q))

variable (A B C)

/-- A polynomial triple determines its commutative square of augmented polynomial algebras. -/
def toPolynomialTower : PolynomialTriple A B C ⥤ Algebra.PolynomialTower A B C where
  obj := towerObj
  map := towerMap
  map_id X := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply Arrow.hom_ext <;> ext x <;> rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply Arrow.hom_ext <;> ext x <;> rfl

/-- Differentials of the first algebra of a polynomial triple, extended to the intermediate base. -/
def inverseImageOmega1 : PolynomialTriple A B C ⥤ ModuleCat.{u} B :=
  toPolynomialTower A B C ⋙ Algebra.PolynomialTower.inverseImageOmega1 A B C

/-- Differentials of the second algebra over the initial base, extended to the final target. -/
def inverseImageOmega2 : PolynomialTriple A B C ⥤ ModuleCat.{u} C :=
  toPolynomialTower A B C ⋙ Algebra.PolynomialTower.inverseImageOmega2 A B C

/-- Relative differentials after tensor base change of a polynomial triple. -/
def inverseImageOmega3 : PolynomialTriple A B C ⥤ ModuleCat.{u} C :=
  toPolynomialTower A B C ⋙ Algebra.PolynomialTower.inverseImageOmega3 A B C

/-- The first differential module of a polynomial triple extended to the final target. -/
def tensorOmega1 : PolynomialTriple A B C ⥤ ModuleCat.{u} C :=
  toPolynomialTower A B C ⋙ Algebra.PolynomialTower.tensorOmega1 A B C

/-- The first differential transitivity map on polynomial triples. -/
def toOmega2 : tensorOmega1 A B C ⟶ inverseImageOmega2 A B C :=
  Functor.whiskerLeft (toPolynomialTower A B C) (Algebra.PolynomialTower.toOmega2 A B C)

/-- The second differential transitivity map on polynomial triples. -/
def toOmega3 : inverseImageOmega2 A B C ⟶ inverseImageOmega3 A B C :=
  Functor.whiskerLeft (toPolynomialTower A B C) (Algebra.PolynomialTower.toOmega3 A B C)

/-- The differential transitivity complex evaluated at a polynomial triple. -/
def omegaSequence_app (X : PolynomialTriple A B C) : ShortComplex (ModuleCat.{u} C) :=
  Algebra.PolynomialTower.omegaSequence_app A B C ((toPolynomialTower A B C).obj X)

/-- The differential transitivity sequence is short exact at every polynomial triple. -/
theorem omegaSequence_app_shortExact (X : PolynomialTriple A B C) :
    (omegaSequence_app A B C X).ShortExact :=
  Algebra.PolynomialTower.omegaSequence_app_shortExact A B C ((toPolynomialTower A B C).obj X)

end RingedSite.Cotangent.PolynomialTriple
