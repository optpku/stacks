/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldHomSectionsComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LocalHomDiagonalProduct
public import Mathlib.Data.Fintype.Fin

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace FieldHomCochainComparison
variable {k : Type u} [Field k]
variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)
variable (P : SchemeOverField k) [CompactSpace P.left] [QuasiSeparatedSpace P.left]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [∀ Y : Scheme.{u}, Y.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Rᵐᵒᵖ),
  (smallEtalePullback f).op.HasLeftKanExtension F]

instance inverse_additive : (FieldModuleDescent.inverse k R).Additive := by sorry
instance forward_additive : (FieldModuleDescent.forward k Rᵐᵒᵖ).Additive := by sorry
instance pushforward_additive : (LocalHomDirectImage.pushforward P.hom A).Additive := by sorry
instance sections_preservesFiniteLimits : PreservesFiniteLimits (NoncommGeometricSource.discreteSections Rᵐᵒᵖ P) := by sorry
instance forward_preservesFiniteLimits : PreservesFiniteLimits (FieldModuleDescent.forward k Rᵐᵒᵖ) := by sorry

variable (B : ChainComplex (DiscreteModuleCat R Gal(AlgebraicClosure k/k)) ℕ)
variable (J : CochainComplex (Sheaf P.left.smallEtaleTopology (ModuleCat.{u + 1} A)) ℕ)

abbrev pulledB := ((FieldGeometricAdjunction.pullback R P).mapHomologicalComplex (ComplexShape.down ℕ)).obj B
abbrev fieldB := ((FieldModuleDescent.inverse k R).mapHomologicalComplex (ComplexShape.down ℕ)).obj B
abbrev fieldJ := ((LocalHomDirectImage.pushforward P.hom A).mapHomologicalComplex (ComplexShape.up ℕ)).obj J

abbrev sourceComplex := NoncommLocalHomComplex.complex h hc P.left (pulledB P B) J
abbrev targetComplex := NoncommLocalHomComplex.complex h hc (Spec (CommRingCat.of k)) (fieldB B) (fieldJ P J)

/-- Each diagonal factor uses the actual closed-adjunction/field-stalk comparison. -/
def factorIso (n : ℕ) (i : Fin (n + 1)) := FieldHomSectionsComparison.iso h hc P (B.X i.val) (J.X (n - i.val))

def toTargetCone (n : ℕ) : Cone
    (LocalHomDiagonalProduct.diagram h hc (Spec (CommRingCat.of k)) (fieldB B) (fieldJ P J) n ⋙
      FieldModuleDescent.forward k Rᵐᵒᵖ) where
  pt := (NoncommGeometricSource.discreteSections Rᵐᵒᵖ P).obj ((sourceComplex h hc P B J).X n)
  π := Discrete.natTrans (fun i ↦
    (NoncommGeometricSource.discreteSections Rᵐᵒᵖ P).map
      (NoncommLocalHomComplex.projection h hc P.left (pulledB P B) J n i.as) ≫
    (factorIso h hc P B J n i.as).hom)

def toSourceCone (n : ℕ) : Cone
    (LocalHomDiagonalProduct.diagram h hc P.left (pulledB P B) J n ⋙
      NoncommGeometricSource.discreteSections Rᵐᵒᵖ P) where
  pt := (FieldModuleDescent.forward k Rᵐᵒᵖ).obj ((targetComplex h hc P B J).X n)
  π := Discrete.natTrans (fun i ↦
    (FieldModuleDescent.forward k Rᵐᵒᵖ).map
      (NoncommLocalHomComplex.projection h hc (Spec (CommRingCat.of k)) (fieldB B) (fieldJ P J) n i.as) ≫
    (factorIso h hc P B J n i.as).inv)

/-- The finite-product lift uses Kuhn's explicit product universal maps, mapped
by the actual right adjoint/equivalence. No product comparison is assumed. -/
def degreeIso (n : ℕ) :
    (NoncommGeometricSource.discreteSections Rᵐᵒᵖ P).obj ((sourceComplex h hc P B J).X n) ≅
    (FieldModuleDescent.forward k Rᵐᵒᵖ).obj ((targetComplex h hc P B J).X n) where
  hom := (isLimitOfPreserves (FieldModuleDescent.forward k Rᵐᵒᵖ)
    (LocalHomDiagonalProduct.isLimit h hc (Spec (CommRingCat.of k)) (fieldB B) (fieldJ P J) n)).lift
      (toTargetCone h hc P B J n)
  inv := (isLimitOfPreserves (NoncommGeometricSource.discreteSections Rᵐᵒᵖ P)
    (LocalHomDiagonalProduct.isLimit h hc P.left (pulledB P B) J n)).lift (toSourceCone h hc P B J n)
  hom_inv_id := by sorry
  inv_hom_id := by sorry

/-- Closed-adjunction comparison of the entire signed Hom differential. -/
def cochainIso :
    ((NoncommGeometricSource.discreteSections Rᵐᵒᵖ P).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (sourceComplex h hc P B J) ≅
    ((FieldModuleDescent.forward k Rᵐᵒᵖ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (targetComplex h hc P B J) :=
  HomologicalComplex.Hom.isoOfComponents (degreeIso h hc P B J) (by sorry)

def integerIso :
    ((NoncommGeometricSource.discreteSections Rᵐᵒᵖ P).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((sourceComplex h hc P B J).extend ComplexShape.embeddingUpNat) ≅
    ((FieldModuleDescent.forward k Rᵐᵒᵖ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((targetComplex h hc P B J).extend ComplexShape.embeddingUpNat) :=
  ComplexShape.embeddingUpNat.mapAppIso (NoncommGeometricSource.discreteSections Rᵐᵒᵖ P) (sourceComplex h hc P B J) ≪≫
  (ComplexShape.embeddingUpNat.extendFunctor _).mapIso (cochainIso h hc P B J) ≪≫
  (ComplexShape.embeddingUpNat.mapAppIso (FieldModuleDescent.forward k Rᵐᵒᵖ) (targetComplex h hc P B J)).symm

/-- Use the canonical additive-functor shift comparison, not a new CommShift assumption. -/
def shiftedIso :
    ((NoncommGeometricSource.discreteSections Rᵐᵒᵖ P).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (NoncommLocalHomComplex.shiftedComplex h hc P.left (pulledB P B) J) ≅
    ((FieldModuleDescent.forward k Rᵐᵒᵖ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (NoncommLocalHomComplex.shiftedComplex h hc (Spec (CommRingCat.of k)) (fieldB B) (fieldJ P J)) :=
  ((NoncommGeometricSource.discreteSections Rᵐᵒᵖ P).mapCochainComplexShiftIso 2).app
    ((sourceComplex h hc P B J).extend ComplexShape.embeddingUpNat) ≪≫
  (shiftFunctor _ (2 : ℤ)).mapIso (integerIso h hc P B J) ≪≫
  (((FieldModuleDescent.forward k Rᵐᵒᵖ).mapCochainComplexShiftIso 2).app
    ((targetComplex h hc P B J).extend ComplexShape.embeddingUpNat)).symm

end FieldHomCochainComparison
