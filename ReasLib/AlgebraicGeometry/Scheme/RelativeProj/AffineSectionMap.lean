/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.AffineSectionRing
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.CanonicalAlgebra
public import ReasLib.AlgebraicGeometry.Scheme.Module.Associated.Affine

/-!
# Actual homogeneous maps to the Serre sheaves of the affine section algebra

A homogeneous section is sent to its homogeneous fraction with denominator1.
The associated-module adjunction turns this linear map into a sheaf map. The
only inverted map is the specified affine quasi-coherent counit.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry Opposite
open SheafOfModules.RingedSite
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.RelativeProjAffineSectionRing

variable {S : Scheme.{u}} (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf)
variable [𝒜.IsCommutative] [IsAffine S]

/-- The actual degree-n section is the fraction a/1, in the shifted regular module. -/
def homogeneousSection (n : ℕ) (a : Γ(𝒜 (n : ℤ), ⊤)) :
    Γ(Proj.AssociatedModule.twistingSheaf (grading 𝒜) (n : ℤ), ⊤) :=
  Proj.AssociatedModule.degreeZeroToGlobalSections (grading 𝒜)
    (Proj.AssociatedModule.GradedMap.regularShift.{u, u} (grading 𝒜) (n : ℤ))
    ⟨(gradeEquiv 𝒜 n a).1, by simpa using (gradeEquiv 𝒜 n a).2⟩

/-- Regard the same actual global section as a section of the direct image. -/
def homogeneousPushforwardSection (n : ℕ) (a : Γ(𝒜 (n : ℤ), ⊤)) :
    Γ((Scheme.Modules.pushforward (toBase 𝒜)).obj
      (Proj.AssociatedModule.twistingSheaf (grading 𝒜) (n : ℤ)), ⊤) :=
  (Proj.AssociatedModule.twistingSheaf (grading 𝒜) (n : ℤ)).val.map
    (eqToHom (show (toBase 𝒜 ⁻¹ᵁ ⊤) = ⊤ from by simp)).op
      (homogeneousSection 𝒜 n a)

/-- The fraction section map is linear for the actual map from the affine base. -/
def homogeneousSectionsMap (n : ℕ) :
    S.toRingedSpace.moduleGlobalSectionsFunctor.obj (𝒜 (n : ℤ)) ⟶
      S.toRingedSpace.moduleGlobalSectionsFunctor.obj
        ((Scheme.Modules.pushforward (toBase 𝒜)).obj
          (Proj.AssociatedModule.twistingSheaf (grading 𝒜) (n : ℤ))) := by
  let M := S.toRingedSpace.moduleGlobalSectionsFunctor.obj (𝒜 (n : ℤ))
  let N := S.toRingedSpace.moduleGlobalSectionsFunctor.obj
    ((Scheme.Modules.pushforward (toBase 𝒜)).obj
      (Proj.AssociatedModule.twistingSheaf (grading 𝒜) (n : ℤ)))
  exact @ModuleCat.ofHom S.toRingedSpace.globalSectionsRing _ M N
    M.isAddCommGroup M.isModule N.isAddCommGroup N.isModule
    { toFun := homogeneousPushforwardSection 𝒜 n
      map_add' := sorry
      map_smul' := sorry }

/-- The homogeneous sheaf map is the adjoint of a/1, preceded by the inverse
of the actual affine associated-module counit. -/
def homogeneousSheafMap (hA : 𝒜.IsQuasicoherent) (n : ℕ) :
    𝒜 (n : ℤ) ⟶ (Scheme.Modules.pushforward (toBase 𝒜)).obj
      (Proj.AssociatedModule.twistingSheaf (grading 𝒜) (n : ℤ)) :=
  (Scheme.Modules.associatedCounitIso S (𝒜 (n : ℤ)) (hA (n : ℤ))).inv ≫
    (RingedSpace.Module.Associated.idHomEquiv S.toRingedSpace _ _).symm
      (homogeneousSectionsMap 𝒜 n)

/-- The same actual map in inverse-image form. -/
def homogeneousPullbackMap (hA : 𝒜.IsQuasicoherent) (n : ℕ) :
    (Scheme.Modules.pullback (toBase 𝒜)).obj (𝒜 (n : ℤ)) ⟶
      Proj.AssociatedModule.twistingSheaf (grading 𝒜) (n : ℤ) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (toBase 𝒜)).homEquiv _ _).symm
    (homogeneousSheafMap 𝒜 hA n)

end AlgebraicGeometry.Scheme.RelativeProjAffineSectionRing
