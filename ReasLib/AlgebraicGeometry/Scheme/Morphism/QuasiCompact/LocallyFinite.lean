/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.Topology.LocallyFinite.Image
public import ReasLib.Topology.Specialization.Dimension

@[expose] public section

open CategoryTheory TopologicalSpace Topology

universe u v

namespace AlgebraicGeometry.Scheme.Hom

/-- A quasi-compact morphism between schemes locally of finite type over a universally catenary
scheme sends a locally finite family of closed subsets to a locally finite family of closures of
their images. -/
theorem locallyFinite_closure_image
    {S X Y : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (pX : X ⟶ S) [LocallyOfFiniteType pX] (pY : Y ⟶ S) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [QuasiCompact f] {I : Type v} (Z : I → Closeds X)
    (hZ : LocallyFinite (fun i ↦ (Z i : Set X))) :
    LocallyFinite (fun i ↦ closure (f.base '' (Z i : Set X))) := sorry

end AlgebraicGeometry.Scheme.Hom
