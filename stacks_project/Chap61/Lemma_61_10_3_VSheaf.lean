/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily.Refinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Covering
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Presentation
public import ReasLib.CategoryTheory.Sites.Family.Sheaf

/-!
# Relative V-sheaf condition

This module owns the family-level V-sheaf condition for set-valued
presheaves on schemes over a fixed base, together with the Zariski plus
singleton standard-V tests and the implication from h-sheaves that preserve
directed affine limits.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry
namespace Scheme.Over

/-- A presheaf on schemes over `S` satisfies the sheaf property for the V
topology when it satisfies the fixed-family sheaf condition for every V
covering in `Over S`. -/
abbrev satisfiesVSheafProperty (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type v) :
    Prop :=
  ∀ {ι : Type w} {T : Over S} (family : ι → Over S) (map : ∀ i, family i ⟶ T),
    IsVCovering T.left (fun i ↦ (family i).left) (fun i ↦ (map i).left) →
      Presheaf.IsSheafForFamily F family map

/-- The relative V-sheaf condition unfolds to sheafness for each V-covering
family in `Over S`. -/
theorem satisfiesVSheafProperty_iff (S : Scheme.{u})
    (F : (Over S)ᵒᵖ ⥤ Type v) :
    satisfiesVSheafProperty.{u, v, w} S F ↔
      ∀ {ι : Type w} {T : Over S} (family : ι → Over S)
        (map : ∀ i, family i ⟶ T),
          IsVCovering T.left (fun i ↦ (family i).left)
              (fun i ↦ (map i).left) →
            Presheaf.IsSheafForFamily F family map := sorry

/-- A relative V sheaf satisfies the fixed-family sheaf condition for every
V-covering family in `Over S`. -/
theorem satisfiesVSheafProperty.isSheafFor {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type v} (hF : satisfiesVSheafProperty.{u, v, w} S F)
    {ι : Type w} {T : Over S} (family : ι → Over S)
    (map : ∀ i, family i ⟶ T)
    (hcover : IsVCovering T.left (fun i ↦ (family i).left)
      (fun i ↦ (map i).left)) :
    Presheaf.IsSheafForFamily F family map := sorry

/-- A presheaf on schemes over `S` satisfies the singleton standard V sheaf
condition when it does so for each affine one-chart family. -/
abbrev satisfiesStandardVSingletonSheafProperty (S : Scheme.{u})
    (F : (Over S)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ {U V : Over S} [IsAffine U.left] [IsAffine V.left] (f : V ⟶ U),
    AffineFamilyOver.IsStandardVCover
        (AffineFamilyOver.singleton f.left inferInstance) →
      Presieve.IsSheafFor F (Presieve.singleton f)

/-- The relative V-sheaf condition is equivalent to the Zariski sheaf
condition on `Over S` together with the singleton standard V tests. -/
theorem satisfiesVSheafProperty_iff_zariski_and_standardVSingleton
    (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type v) :
    satisfiesVSheafProperty.{u, v, w} S F ↔
      Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F ∧
        satisfiesStandardVSingletonSheafProperty S F := sorry

/-- An h-sheaf on all schemes over `S` that preserves directed affine limits
satisfies the sheaf property for the V topology. -/
theorem satisfiesVSheafProperty_of_isHSheaf_of_preservesDirectedAffineLimits
    {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v)
    (hF_h : Presheaf.IsSheaf ((Scheme.hPrecoverage.toGrothendieck).over S) F)
    (hF_limits : PreservesDirectedAffineLimits S F) :
    satisfiesVSheafProperty.{u, v, w} S F := sorry

end Scheme.Over
end AlgebraicGeometry
