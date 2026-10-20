/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.Acyclicity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.Functoriality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ClosedSubset
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.RingedSpace

@[expose] public section

open AlgebraicGeometry CategoryTheory SheafOfModules.ClosedSubset
open SheafOfModules.ClosedSubset.SupportedDerived

noncomputable section

universe u

namespace ModuleCech

variable {X : Scheme.{u}}

/-- The principal-open Čech functor viewed in the derived category. -/
noncomputable def ofSectionsDerivedFunctor {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    X.Modules ⥤ RingedSpace.ModuleDerived X.toRingedSpace :=
  ofSectionsFunctor f ⋙ toRingedSpaceDerived X

/-- The canonical natural map from the derived principal-open Čech complex to its original
module in degree zero. -/
noncomputable def ofSectionsProjectionDerived {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    ofSectionsDerivedFunctor f ⟶ moduleToDerived X :=
  Functor.whiskerRight (ofSectionsProjection f) (toRingedSpaceDerived X)

/-- The common closed zero locus of a finite family of global sections. -/
def ofSectionsZeroLocus {c : ℕ} (f : Fin c → Γ(X, ⊤)) : TopologicalSpace.Closeds X :=
  ⟨X.zeroLocus (Set.range f), X.zeroLocus_isClosed _⟩

/-- The common zero locus has the expected underlying set. -/
theorem coe_ofSectionsZeroLocus {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    (ofSectionsZeroLocus f : Set X) = X.zeroLocus (Set.range f) := sorry

/-- The derived principal-open extended Čech complex has cohomology supported on the common
zero locus of the chosen global sections. -/
@[stacks 0G7L]
theorem ofSectionsDerived_isSupportedOn {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (ℱ : X.Modules) :
    RingedSpace.ModuleDerived.IsSupportedOn
      ((ofSectionsDerivedFunctor f).obj ℱ) (ofSectionsZeroLocus f) := sorry

/-- The canonical map from the derived principal-open Čech complex to the module in degree
zero factors naturally through the closed-support coreflector. -/
@[stacks 0G7L]
noncomputable def ofSectionsToLocalCohomology {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    ofSectionsDerivedFunctor f ⟶
      moduleToDerived X ⋙
        coreflector
          X.toRingedSpace.ringCatSheaf (ofSectionsZeroLocus f) ⋙
        inclusion
          X.toRingedSpace.ringCatSheaf (ofSectionsZeroLocus f) where
  app ℱ :=
    (((adjunction
      X.toRingedSpace.ringCatSheaf (ofSectionsZeroLocus f)).homEquiv
        ⟨(ofSectionsDerivedFunctor f).obj ℱ, ofSectionsDerived_isSupportedOn f ℱ⟩
        ((moduleToDerived X).obj ℱ)) ((ofSectionsProjectionDerived f).app ℱ)).hom
  naturality _ _ _ := sorry

/-- The canonical factor through closed-support local cohomology, followed by the coreflection
counit, is the degree-zero projection. -/
@[stacks 0G7L]
theorem ofSectionsToLocalCohomology_triangle {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (ℱ : X.Modules) :
    (ofSectionsToLocalCohomology f).app ℱ ≫
      (adjunction
        X.toRingedSpace.ringCatSheaf (ofSectionsZeroLocus f)).counit.app
          ((moduleToDerived X).obj ℱ) =
      (ofSectionsProjectionDerived f).app ℱ := sorry

/-- For a quasi-coherent module sheaf, the canonical comparison from the derived
principal-open Čech complex to local cohomology on the common zero locus is an isomorphism. -/
@[stacks 0G7M]
instance ofSectionsToLocalCohomology_isIso {X : Scheme.{u}} {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIso ((ofSectionsToLocalCohomology f).app ℱ) := sorry

end ModuleCech

end
