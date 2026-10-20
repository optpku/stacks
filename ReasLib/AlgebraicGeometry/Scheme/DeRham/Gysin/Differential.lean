/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Differential compatibility for equation Gysin morphisms

This file defines coefficient-restricted equation Gysin objects, their induced relative
de Rham differentials, and the compatibility law between them.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DeRham
namespace Gysin

variable {X S : Scheme.{u}}

/-- Right wedge multiplication by an ordered equation form commutes with the relative de Rham differential after coefficient restriction. -/
theorem wedgeWithEquations_d (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    (SheafOfModules.RingedSite.restrictionAlong
          (RingedSpace.DeRham.structureMap q.toLRSHom.toShHom)).map
        ((Scheme.Modules.toRingedSpace X).map (wedgeWithEquations q fs p)) ≫
        RingedSpace.DeRham.d q.toLRSHom.toShHom (p + c) =
      RingedSpace.DeRham.d q.toLRSHom.toShHom p ≫
        (SheafOfModules.RingedSite.restrictionAlong
          (RingedSpace.DeRham.structureMap q.toLRSHom.toShHom)).map
            ((Scheme.Modules.toRingedSpace X).map
              (wedgeWithEquations q fs (p + 1))) ≫
        eqToHom (congrArg (RingedSpace.DeRham.term q.toLRSHom.toShHom)
          (Nat.add_right_comm p 1 c)) := sorry

/-- The coefficient ring sheaf `q⁻¹𝒪_S` restricted to the common zero locus of `fs`. -/
abbrev closedCoefficients (q : X ⟶ S) {c : ℕ} (fs : Fin c → Γ(X, ⊤)) :=
  (TopCat.Sheaf.pullback RingCat.{u}
    (SheafOfModules.ClosedSubset.inclusion (ModuleCech.ofSectionsZeroLocus fs))).obj
      (TopCat.Sheaf.ringSheafOfComm.{u, u}
        (RingedSpace.DeRham.coefficients q.toLRSHom.toShHom))

/-- The restricted coefficient-ring map from `q⁻¹𝒪_S` to `𝒪_X` on the common zero locus. -/
abbrev closedStructureMap (q : X ⟶ S) {c : ℕ} (fs : Fin c → Γ(X, ⊤)) :
    closedCoefficients q fs ⟶
      SheafOfModules.ClosedSubset.ringSheaf X.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus fs) :=
  (TopCat.Sheaf.pullback RingCat.{u}
    (SheafOfModules.ClosedSubset.inclusion (ModuleCech.ofSectionsZeroLocus fs))).map
      (TopCat.Sheaf.ringSheafOfCommMap.{u, u}
        (RingedSpace.DeRham.structureMap q.toLRSHom.toShHom))

/-- Restriction of `𝒪_Z`-modules to modules over the coefficient sheaf from `S`. -/
abbrev coefficientRestriction (q : X ⟶ S) {c : ℕ} (fs : Fin c → Γ(X, ⊤)) :=
  SheafOfModules.restrictScalars (closedStructureMap q fs)

/-- Ambient relative forms pulled to the common zero locus and regarded over the restricted coefficient sheaf. -/
abbrev restrictedForm (q : X ⟶ S) {c : ℕ} (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :=
  (coefficientRestriction q fs).obj
    ((ModuleCech.LocalCohomology.pullbackFunctor fs).obj (relativeForm q p))

/-- The quotient presentation of relative forms on the zero locus, regarded over the restricted coefficient sheaf. -/
abbrev restrictedSource (q : X ⟶ S) {c : ℕ} (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :=
  (coefficientRestriction q fs).obj (source q fs p)

/-- Degree-`c` local cohomology of ambient relative forms, regarded over the restricted coefficient sheaf. -/
abbrev restrictedTarget (q : X ⟶ S) {c : ℕ} (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :=
  (coefficientRestriction q fs).obj
    ((ModuleCech.LocalCohomology.cohomologyFunctor fs).obj (relativeForm q p))

/-- The canonical map from restricted ambient forms to their quotient presentation on the zero locus. -/
noncomputable def ambientToSource (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    restrictedForm q fs p ⟶ restrictedSource q fs p :=
  (coefficientRestriction q fs).map
    ((ModuleCech.LocalCohomology.pullbackQuotientProjection fs).app (relativeForm q p) ≫
      projection q fs p)

/-- The canonical class map from restricted ambient forms to degree-`c` local cohomology. -/
noncomputable def ambientToTarget (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    restrictedForm q fs p ⟶ restrictedTarget q fs p :=
  (coefficientRestriction q fs).map
    ((ModuleCech.LocalCohomology.classMap fs).app (relativeForm q p))

/-- Right wedge multiplication by the ordered equation differentials after coefficient restriction. -/
noncomputable def restrictedWedgeWithEquations (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    restrictedForm q fs p ⟶ restrictedForm q fs (p + c) :=
  (coefficientRestriction q fs).map
    ((ModuleCech.LocalCohomology.pullbackFunctor fs).map
      (wedgeWithEquations q fs p))

/-- Restriction of an ambient relative form agrees with the pullback of its coefficient-linear term. -/
theorem restrictedForm_eq_pullbackTerm (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    restrictedForm q fs p =
      (SheafOfModules.Subset.pullback
        (TopCat.Sheaf.ringSheafOfComm
          (RingedSpace.DeRham.coefficients q.toLRSHom.toShHom))
        (ModuleCech.ofSectionsZeroLocus fs)).obj
          (RingedSpace.DeRham.term q.toLRSHom.toShHom p) := sorry

/-- The relative de Rham differential restricted to the common zero locus of `fs`. -/
noncomputable def restrictedAmbientDifferential (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    restrictedForm q fs p ⟶ restrictedForm q fs (p + 1) :=
  eqToHom (restrictedForm_eq_pullbackTerm q fs p) ≫
    (SheafOfModules.Subset.pullback
      (TopCat.Sheaf.ringSheafOfComm
        (RingedSpace.DeRham.coefficients q.toLRSHom.toShHom))
      (ModuleCech.ofSectionsZeroLocus fs)).map
        (RingedSpace.DeRham.d q.toLRSHom.toShHom p) ≫
    eqToHom (restrictedForm_eq_pullbackTerm q fs (p + 1)).symm

/-- The canonical projection from restricted ambient forms onto the quotient presentation is an epimorphism. -/
noncomputable instance ambientToSource_epi (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    Epi (ambientToSource q fs p) := sorry

/-- The ambient differential followed by the next quotient projection kills the kernel of the current quotient projection. -/
theorem kernel_ι_d_ambientToSource (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    kernel.ι (ambientToSource q fs p) ≫ restrictedAmbientDifferential q fs p ≫
      ambientToSource q fs (p + 1) = 0 := sorry

/-- The de Rham differential induced on the quotient presentation of forms on the zero locus. -/
noncomputable def sourceDifferential (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    restrictedSource q fs p ⟶ restrictedSource q fs (p + 1) :=
  Abelian.epiDesc (ambientToSource q fs p)
    (restrictedAmbientDifferential q fs p ≫ ambientToSource q fs (p + 1))
    (kernel_ι_d_ambientToSource q fs p)

/-- The canonical class map from restricted ambient forms onto degree-`c` local cohomology is an epimorphism. -/
noncomputable instance ambientToTarget_epi (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    Epi (ambientToTarget q fs p) := sorry

/-- The restricted ambient differential followed by the next local-cohomology class map kills the kernel of the current class map. -/
theorem kernel_ι_d_ambientToTarget (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    kernel.ι (ambientToTarget q fs p) ≫ restrictedAmbientDifferential q fs p ≫
      ambientToTarget q fs (p + 1) = 0 := sorry

/-- The canonical coefficient-linear de Rham differential on degree-`c` local cohomology. -/
noncomputable def targetDifferential (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    restrictedTarget q fs p ⟶ restrictedTarget q fs (p + 1) :=
  Abelian.epiDesc (ambientToTarget q fs p)
    (restrictedAmbientDifferential q fs p ≫ ambientToTarget q fs (p + 1))
    (kernel_ι_d_ambientToTarget q fs p)

/-- The equation Gysin morphism after coefficient restriction. -/
noncomputable def restrictedMap (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    restrictedSource q fs p ⟶ restrictedTarget q fs (p + c) :=
  (coefficientRestriction q fs).map (map q fs p)

/-- The source differential is characterized by compatibility with the projection from restricted ambient relative forms. -/
theorem ambientToSource_d (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    ambientToSource q fs p ≫ sourceDifferential q fs p =
      restrictedAmbientDifferential q fs p ≫ ambientToSource q fs (p + 1) := sorry

/-- The local-cohomology differential is characterized by naturality of the canonical class map from restricted ambient forms. -/
theorem ambientToTarget_d (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    ambientToTarget q fs p ≫ targetDifferential q fs p =
      restrictedAmbientDifferential q fs p ≫ ambientToTarget q fs (p + 1) := sorry

/-- Restricted right wedge multiplication by the ordered equation form commutes with the canonical ambient de Rham differentials. -/
theorem restrictedWedgeWithEquations_d (q : X ⟶ S) {c : ℕ}
    (fs : Fin c → Γ(X, ⊤)) (p : ℕ) :
    restrictedWedgeWithEquations q fs p ≫
        restrictedAmbientDifferential q fs (p + c) =
      restrictedAmbientDifferential q fs p ≫
        restrictedWedgeWithEquations q fs (p + 1) ≫
        eqToHom (congrArg (restrictedForm q fs) (Nat.add_right_comm p 1 c)) := sorry

/-- The equation Gysin morphism commutes with the induced relative de Rham differentials. -/
theorem map_d (q : X ⟶ S) {c : ℕ} (fs : Fin c → Γ(X, ⊤))
    (p : ℕ) :
    restrictedMap q fs p ≫ targetDifferential q fs (p + c) =
      sourceDifferential q fs p ≫ restrictedMap q fs (p + 1) ≫
        eqToHom (congrArg (restrictedTarget q fs) (Nat.add_right_comm p 1 c)) := sorry

end Gysin
end DeRham
end Scheme
end AlgebraicGeometry

end
