/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Local

/-!
# Étale morphisms are locally quasi-finite
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Etale

/-- An étale morphism of schemes is locally quasi-finite. -/
theorem locallyQuasiFinite {X S : Scheme.{u}} {f : X ⟶ S} (h : Etale f) :
    LocallyQuasiFinite f := sorry

/-- Étale morphisms have the canonical locally quasi-finite structure. -/
instance instLocallyQuasiFinite {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] :
    LocallyQuasiFinite f :=
  locallyQuasiFinite (inferInstance : Etale f)

end AlgebraicGeometry.Etale
