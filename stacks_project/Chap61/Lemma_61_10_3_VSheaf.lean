/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Over

/-!
# Relative V-sheaf condition

The relative V-sheaf predicates, their family and singleton tests, and the
implication from limit-preserving h-sheaves are available from their shared
mathematical owner with the following types.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Scheme.Over

universe u v w

#check (AlgebraicGeometry.Scheme.Over.satisfiesVSheafProperty.{u, v, w} :
  ∀ (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type v), Prop)

#check (AlgebraicGeometry.Scheme.Over.satisfiesVSheafProperty_iff :
  ∀ (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type v),
    satisfiesVSheafProperty.{u, v, w} S F ↔
      ∀ {ι : Type w} {T : Over S} (family : ι → Over S)
        (map : ∀ i, family i ⟶ T),
          IsVCovering T.left (fun i ↦ (family i).left)
              (fun i ↦ (map i).left) →
            Presheaf.IsSheafForFamily F family map)

#check (AlgebraicGeometry.Scheme.Over.satisfiesVSheafProperty.isSheafFor :
  ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v},
    satisfiesVSheafProperty.{u, v, w} S F →
      ∀ {ι : Type w} {T : Over S} (family : ι → Over S)
        (map : ∀ i, family i ⟶ T),
          IsVCovering T.left (fun i ↦ (family i).left)
              (fun i ↦ (map i).left) →
            Presheaf.IsSheafForFamily F family map)

#check (AlgebraicGeometry.Scheme.Over.satisfiesStandardVSingletonSheafProperty :
  ∀ (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type v), Prop)

#check
  (AlgebraicGeometry.Scheme.Over.satisfiesVSheafProperty_iff_zariski_and_standardVSingleton :
    ∀ (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type v),
      satisfiesVSheafProperty.{u, v, w} S F ↔
        Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F ∧
          satisfiesStandardVSingletonSheafProperty S F)

#check
  (AlgebraicGeometry.Scheme.Over.satisfiesVSheafProperty_of_isHSheaf_of_preservesDirectedAffineLimits :
    ∀ {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v),
      Presheaf.IsSheaf ((Scheme.hPrecoverage.toGrothendieck).over S) F →
        PreservesDirectedAffineLimits S F →
          satisfiesVSheafProperty.{u, v, w} S F)
