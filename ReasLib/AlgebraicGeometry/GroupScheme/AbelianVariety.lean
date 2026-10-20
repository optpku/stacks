/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- An abelian variety over `k` is a group scheme whose structure morphism is
geometrically integral and whose underlying scheme over `k` is a proper variety. -/
class AbelianVariety (G : SchemeOverField k) [CategoryTheory.GrpObj G] : Prop where
  /-- The underlying scheme over `k` is a proper variety. -/
  toProperVariety : ProperVariety G
  /-- The structure morphism is geometrically integral. -/
  toGeometricallyIntegral : GeometricallyIntegral G.hom

/-- A proper geometrically integral group scheme over `k` is an abelian variety. -/
instance instAbelianVariety (G : SchemeOverField k) [CategoryTheory.GrpObj G]
    [ProperVariety G] [GeometricallyIntegral G.hom] : AbelianVariety G where
  toProperVariety := inferInstance
  toGeometricallyIntegral := inferInstance

/-- An abelian variety over `k` is a proper variety. -/
instance instProperVarietyOfAbelianVariety (G : SchemeOverField k) [CategoryTheory.GrpObj G]
    [h : AbelianVariety G] : ProperVariety G :=
  h.toProperVariety

/-- The structure morphism of an abelian variety over `k` is geometrically integral. -/
instance instGeometricallyIntegralOfAbelianVariety
    (G : SchemeOverField k) [CategoryTheory.GrpObj G] [h : AbelianVariety G] :
    GeometricallyIntegral G.hom :=
  h.toGeometricallyIntegral

namespace AbelianVariety

/-- The group object underlying an abelian variety is commutative. -/
instance instIsCommMonObj {k : Type u} [Field k] (G : SchemeOverField k)
    [CategoryTheory.GrpObj G] [AbelianVariety G] : CategoryTheory.IsCommMonObj G := by
  simpa using AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral G

end AbelianVariety

/-- An abelian variety is precisely a proper variety with geometrically integral structure
morphism, once its group-scheme structure is fixed. -/
theorem abelianVariety_iff (G : SchemeOverField k) [CategoryTheory.GrpObj G] :
    AbelianVariety G ↔ ProperVariety G ∧ GeometricallyIntegral G.hom := sorry

end AlgebraicGeometry
