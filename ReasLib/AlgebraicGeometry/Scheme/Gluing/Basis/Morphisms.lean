/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gluing.Basis.Basic

/-!
# Morphisms of basis-indexed scheme gluings

This module provides compatibility and realization predicates for morphisms between
basis-indexed scheme gluing data, together with the canonical restriction of a global map.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.BasisSchemeGluing

/-- A family of local scheme morphisms is compatible when it lies over the identified basis
opens and commutes with every transition morphism. -/
def IsMorphismCompatible {S : Scheme.{u}}
    (D E : BasisSchemeGluing.{u, v} S) (indexEquiv : D.ι ≃ E.ι)
    (localMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i)) : Prop :=
  (∀ i : D.ι, E.U (indexEquiv i) = D.U i) ∧
    (∀ i : D.ι, localMap i ≫ E.localToBase (indexEquiv i) = D.localToBase i) ∧
      ∀ ⦃i j : D.ι⦄ (hij : D.U i ≤ D.U j)
        (hij' : E.U (indexEquiv i) ≤ E.U (indexEquiv j)),
        D.rho hij ≫ localMap j = localMap i ≫ E.rho hij'

/-- The canonical restriction of a global map over the base to corresponding basis-open
preimages in two equipped realizations. -/
noncomputable def restrictedMap {S : Scheme.{u}}
    (D E : BasisSchemeGluing.{u, v} S) (indexEquiv : D.ι ≃ E.ι)
    (localMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i))
    (compatible : D.IsMorphismCompatible E indexEquiv localMap)
    (R : D.Realization) (R' : E.Realization) (globalMap : R.Y ⟶ R'.Y)
    (overBase : globalMap ≫ R'.toBase = R.toBase) (i : D.ι) :
    (R.toBase ⁻¹ᵁ D.U i).toScheme ⟶
      (R'.toBase ⁻¹ᵁ E.U (indexEquiv i)).toScheme :=
  globalMap.resLE (R'.toBase ⁻¹ᵁ E.U (indexEquiv i))
    (R.toBase ⁻¹ᵁ D.U i) (by
      rw [← compatible.1 i, ← Scheme.Hom.comp_preimage, overBase])

/-- The canonical restriction of a global map followed by the target open inclusion equals
the source open inclusion followed by the global map. -/
theorem restrictedMap_ι {S : Scheme.{u}}
    (D E : BasisSchemeGluing.{u, v} S) (indexEquiv : D.ι ≃ E.ι)
    (localMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i))
    (compatible : D.IsMorphismCompatible E indexEquiv localMap)
    (R : D.Realization) (R' : E.Realization) (globalMap : R.Y ⟶ R'.Y)
    (overBase : globalMap ≫ R'.toBase = R.toBase) (i : D.ι) :
    D.restrictedMap E indexEquiv localMap compatible R R' globalMap overBase i ≫
        (R'.toBase ⁻¹ᵁ E.U (indexEquiv i)).ι =
      (R.toBase ⁻¹ᵁ D.U i).ι ≫ globalMap := sorry

/-- A global morphism between equipped realizations realizes a compatible family of local
morphisms when it lies over the base and its canonical restrictions recover every local map. -/
def IsRealizationMap {S : Scheme.{u}}
    (D E : BasisSchemeGluing.{u, v} S) (indexEquiv : D.ι ≃ E.ι)
    (localMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i))
    (compatible : D.IsMorphismCompatible E indexEquiv localMap)
    (R : D.Realization) (R' : E.Realization) (globalMap : R.Y ⟶ R'.Y) : Prop :=
  ∃ overBase : globalMap ≫ R'.toBase = R.toBase,
    ∀ i : D.ι,
      (R.localIso i).hom ≫ localMap i =
        D.restrictedMap E indexEquiv localMap compatible R R' globalMap overBase i ≫
          (R'.localIso (indexEquiv i)).hom

/-- Compatible local morphisms between basis-indexed scheme gluing data induce a global
morphism between arbitrary equipped realizations that recovers all local morphisms. -/
theorem existsRealizationMap {S : Scheme.{u}}
    (D E : BasisSchemeGluing.{u, v} S) (indexEquiv : D.ι ≃ E.ι)
    (localMap : ∀ i : D.ι, D.X i ⟶ E.X (indexEquiv i))
    (compatible : D.IsMorphismCompatible E indexEquiv localMap)
    (R : D.Realization) (R' : E.Realization) :
    ∃ globalMap : R.Y ⟶ R'.Y,
      D.IsRealizationMap E indexEquiv localMap compatible R R' globalMap := sorry

end AlgebraicGeometry.Scheme.BasisSchemeGluing
