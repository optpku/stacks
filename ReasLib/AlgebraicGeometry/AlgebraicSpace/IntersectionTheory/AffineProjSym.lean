/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra.QuotientChart
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.CanonicalAlgebra
public import ReasLib.AlgebraicGeometry.Scheme.Module.Associated.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.CategoryTheory.Monoidal.InvertibleQuotient

/-! Actual affine Proj(Sym Γ(E)) and its generator-to-O(1) quotient map. -/
@[expose] public section
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.AffineProjSym
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

abbrev grading := Proj.SymmetricQuotientChart.grading R M

/-- The carrier is the actual projective spectrum of the actual symmetric algebra. -/
def scheme : Scheme.{u} := Proj (grading R M)

/-- Constants land in the degree-zero piece of Sym M. -/
def baseToZero : R →+* grading R M 0 where
  toFun r := ⟨algebraMap R (SymmetricAlgebra R M) r, by
    simpa only [grading, Proj.SymmetricQuotientChart.grading, pow_zero] using
      (Submodule.mem_one.mpr ⟨r, rfl⟩)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

/-- The actual structure morphism, with no supplied projective presentation. -/
def toSpec : scheme R M ⟶ Spec (.of R) :=
  Proj.toSpecZero (grading R M) ≫ Spec.map (CommRingCat.ofHom (baseToZero R M))

/-- Actual Serre twist of the shifted regular grading. -/
def O1 : (scheme R M).Modules :=
  Proj.AssociatedModule.twistingSheaf (grading R M) 1

/-- Generator m becomes the homogeneous section iota(m)/1 of O(1). -/
def generatorSection (m : M) : Γ(O1 R M, ⊤) :=
  Proj.AssociatedModule.degreeZeroToGlobalSections (grading R M)
    (Proj.AssociatedModule.GradedMap.regularShift (grading R M) 1)
    ⟨SymmetricAlgebra.ι R M m, Proj.SymmetricQuotientChart.generator_mem_degreeOne m⟩

variable {Y : Scheme.{u}} [IsAffine Y] (E : Y.Modules) [E.IsQuasicoherent]

/-- The ring and module are the genuine affine global sections of E. -/
abbrev baseRing : CommRingCat.{u} := Y.presheaf.obj (op ⊤)
abbrev sections : ModuleCat (baseRing (Y := Y)) := Y.toRingedSpace.moduleGlobalSectionsFunctor.obj E

/-- Projectivization over the affine scheme uses its actual module of sections. -/
def overScheme : Scheme.{u} := scheme (baseRing (Y := Y)) (sections E)

def projection : overScheme E ⟶ Y :=
  toSpec (baseRing (Y := Y)) (sections E) ≫ Y.isoSpec.inv

def line : (overScheme E).Modules := O1 (baseRing (Y := Y)) (sections E)

/-- The fraction section, regarded in the direct image over Y. -/
def sectionToPushforward (m : sections E) :
    Γ((Scheme.Modules.pushforward (projection E)).obj (line E), ⊤) :=
  (line E).val.map (eqToHom (show projection E ⁻¹ᵁ ⊤ = ⊤ by simp)).op
    (generatorSection (baseRing (Y := Y)) (sections E) m)

/-- Linearity is for the specified structure morphism and generator map. -/
def sectionMap : sections E ⟶ Y.toRingedSpace.moduleGlobalSectionsFunctor.obj
    ((Scheme.Modules.pushforward (projection E)).obj (line E)) := by
  let M0 := Y.toRingedSpace.moduleGlobalSectionsFunctor.obj E
  let N := Y.toRingedSpace.moduleGlobalSectionsFunctor.obj
    ((Scheme.Modules.pushforward (projection E)).obj (line E))
  exact @ModuleCat.ofHom Y.toRingedSpace.globalSectionsRing _ M0 N
    M0.isAddCommGroup M0.isModule N.isAddCommGroup N.isModule
    { toFun := sectionToPushforward E
      map_add' := by sorry
      map_smul' := by sorry }

/-- The actual affine counit identifies E with its associated section sheaf;
the map is the adjoint of m ↦ iota(m)/1. -/
def sheafMap : E ⟶ (Scheme.Modules.pushforward (projection E)).obj (line E) :=
  (Scheme.Modules.associatedCounitIso Y E inferInstance).inv ≫
      (RingedSpace.Module.Associated.idHomEquiv Y.toRingedSpace _ _).symm (sectionMap E)

def quotientHom : (Scheme.Modules.pullback (projection E)).obj E ⟶ line E :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (projection E)).homEquiv _ _).symm (sheafMap E)

/-- The symmetric algebra is generated in degree one, so its actual O(1) is invertible. -/
theorem line_invertible : isInvertibleObject (line E) := by
  sorry

/-- Homogeneous degree-one generators cover Proj, so the specified quotient is epi. -/
theorem quotientHom_epi : Epi (quotientHom E) := by
  sorry

def quotient : CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback (projection E)).obj E) where
  object := line E
  isInvertible := line_invertible E
  hom := quotientHom E
  hom_epi := quotientHom_epi E

theorem quotient_hom : (quotient E).hom = quotientHom E := rfl
theorem quotient_object : (quotient E).object = line E := rfl

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.AffineProjSym
