/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement

/-!
# Locally closed strata from ideal sheaves

This module constructs the locally closed stratum between two successive ideal-sheaf stages and
its structural morphism to the ambient scheme.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The locally closed stratum obtained by removing the next closed stage from the current one. -/
noncomputable def stratumOpen {S : Scheme.{u}} {t : ℕ}
    (Z : Fin (t + 1) → S.IdealSheafData) (i : Fin t) :
    (Z i.castSucc).subscheme.Opens :=
  ((Z i.succ).comap (Z i.castSucc).subschemeι).openComplement

/-- The locally closed stratum is the open complement of the next stage in the current stage. -/
theorem stratumOpen_def {S : Scheme.{u}} {t : ℕ}
    (Z : Fin (t + 1) → S.IdealSheafData) (i : Fin t) :
    stratumOpen Z i =
      ((Z i.succ).comap (Z i.castSucc).subschemeι).openComplement := sorry

/-- The structural morphism from a locally closed stratum to the ambient scheme. -/
noncomputable def stratumMap {S : Scheme.{u}} {t : ℕ}
    (Z : Fin (t + 1) → S.IdealSheafData) (i : Fin t) :
    (stratumOpen Z i).toScheme ⟶ S :=
  (stratumOpen Z i).ι ≫ (Z i.castSucc).subschemeι

/-- The structural morphism of a stratum is its open immersion followed by the closed immersion. -/
theorem stratumMap_def {S : Scheme.{u}} {t : ℕ}
    (Z : Fin (t + 1) → S.IdealSheafData) (i : Fin t) :
    stratumMap Z i = (stratumOpen Z i).ι ≫ (Z i.castSucc).subschemeι := sorry

end AlgebraicGeometry.Scheme.Modules
