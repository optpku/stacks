/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsPureAlong

/-- A finite type quasicoherent module that is flat at every point of a fibre and pure
along that fibre is universally pure along it. -/
theorem universally_of_flatOverAt {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.FiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (s : S) (h_pure : F.IsPureAlong f s)
    (h_flat : ∀ x : f.fiber s, flatOverAt F f (f.fiberι s x)) :
    F.IsUniversallyPureAlong f s := sorry

end AlgebraicGeometry.Scheme.Modules.IsPureAlong

namespace AlgebraicGeometry.Scheme.Modules.IsPureOver

/-- For a finite type morphism, a finite type quasicoherent module that is flat over the
base is pure over the base if and only if it is universally pure over the base. -/
theorem iff_universally_of_flatOver {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.FiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_flat : flatOver F f) :
    F.IsPureOver f ↔ F.IsUniversallyPureOver f := sorry

end AlgebraicGeometry.Scheme.Modules.IsPureOver
