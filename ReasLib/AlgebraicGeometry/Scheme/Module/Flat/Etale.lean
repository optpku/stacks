/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.Algebra.Module.Flat.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat

/-!
# Relative flatness over an étale base

This module records that relative flatness of a quasi-coherent scheme module is unchanged after
composing the base morphism with an étale morphism.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme.Modules

/-- Relative flatness of a quasi-coherent scheme module at a point is unchanged after composing
the base morphism with an étale morphism. -/
theorem flatOverAt_comp_iff_of_etale {X T S : Scheme.{u}}
    (f : X ⟶ T) (g : T ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    [Etale g] (x : X) :
    flatOverAt ℱ (f ≫ g) x ↔ flatOverAt ℱ f x := sorry

/-- Relative flatness of a quasi-coherent scheme module is unchanged after composing the base
morphism with an étale morphism. -/
theorem flatOver_comp_iff_of_etale {X T S : Scheme.{u}}
    (f : X ⟶ T) (g : T ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    [Etale g] :
    flatOver ℱ (f ≫ g) ↔ flatOver ℱ f := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Etale

/-- For an étale morphism, a module over the source stalk is flat after restriction to the
target stalk if and only if it is flat over the source stalk. -/
theorem flatAlong_stalkMap_iff {T S : Scheme.{u}} (f : T ⟶ S) [Etale f]
    (t : T) (M : Type v) [AddCommGroup M] [Module (T.presheaf.stalk t) M] :
    Module.FlatAlong (f.stalkMap t).hom M ↔ Module.Flat (T.presheaf.stalk t) M := sorry

end AlgebraicGeometry.Etale
