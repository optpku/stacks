/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Adic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.CompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.GeometricCompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.CohomologicalLFunction

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

variable {k : Type u} [Field k] [Fintype k]
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom] [IsNoetherian X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [Etale (Compactification.Of.ι P)]
variable [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [HasWeakSheafify (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u}]
variable [HasSheafify (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u})]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable (F : ZEllSheaf X.left ℓ)

/- Geometric compactly supported rational ℓ-adic cohomology. -/
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.geometricCohomologyCompactSupportQEll P F :
  ℕ → ModuleCat.{u} ℚ_[ℓ])

/- Geometric Frobenius on geometric compactly supported rational cohomology. -/
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.geometricFrobenius_cohomologyCompactSupportQEll
  P F : ∀ i : ℕ, Module.End ℚ_[ℓ] (geometricCohomologyCompactSupportQEll P F i))

/- The bounded product of signed cohomological Euler factors. -/
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.cohomologicalLFunction P F :
  ℕ → PowerSeries ℚ_[ℓ])

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
