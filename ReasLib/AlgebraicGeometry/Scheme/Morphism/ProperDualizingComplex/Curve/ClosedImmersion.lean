/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ClosedImmersion.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Immersion

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived
open RingedSpace.Hom
open RingedSpace.Hom.ModulePushforward.ClosedImmersion
open RingedSpace.ModuleDerived.ClosedImmersion

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DerivedQCoh
namespace ProperDualizingComplex

/-- For a closed immersion into a proper curve over a field, the proper dualizing complex of the
source is the derived internal Hom from its structure sheaf into the ambient proper dualizing
complex. -/
theorem properDualizingComplex_closedImmersion
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    {Y : Scheme.{u}} (i : Y ⟶ X.left) [IsClosedImmersion i]
    (h_dimension : topologicalKrullDim X.left ≤ 1) :
    IsIsomorphic (properDualizingComplex (i ≫ X.hom)).obj
      ((rHomFromStructureSheaf i.toShHom (IsClosedImmersion.isClosedEmbedding i)).obj
        (properDualizingComplex X.hom).obj) := sorry

/-- For a closed immersion into a proper curve over a field, the curve dualizing module of the
source is the internal Hom from its structure sheaf into the ambient curve dualizing module. -/
theorem curveDualizingModule_closedImmersion
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    {Y : Scheme.{u}} (i : Y ⟶ X.left) [IsClosedImmersion i]
    (h_dimension : topologicalKrullDim X.left ≤ 1) :
    IsIsomorphic (curveDualizingModule (i ≫ X.hom))
      ((homFromStructureSheaf i.toShHom (IsClosedImmersion.isClosedEmbedding i)).obj
        (curveDualizingModule X.hom)) := sorry

/-- For a closed immersion into a proper curve over a field, the pushforward of the curve
dualizing module is the ambient internal Hom from the pushed-forward structure sheaf. -/
theorem pushforward_curveDualizingModule_closedImmersion
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    {Y : Scheme.{u}} (i : Y ⟶ X.left) [IsClosedImmersion i]
    (h_dimension : topologicalKrullDim X.left ≤ 1) :
    IsIsomorphic
      ((pushforward i.toShHom).obj (curveDualizingModule (i ≫ X.hom)))
      ((ambientInternalHom i.toShHom).obj (curveDualizingModule X.hom)) := sorry

end ProperDualizingComplex
end DerivedQCoh
end Scheme
end AlgebraicGeometry
