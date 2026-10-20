/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactificationChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NormalizedKummerTrace

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.AssociatedModule
noncomputable section
universe u

namespace ActualNormalizedTraceTransport
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (C D : SchemeOverField k)
variable [Curve C] [Smooth C.hom] [Projective C.hom]
variable [Curve D] [Smooth D.hom] [Projective D.hom]
variable [HasSheafify C.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify D.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf C.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasExt.{u + 1} (Sheaf D.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable (n : ℕ) (hpos : 0 < n) (hn : IsUnit (n : k))

/-- Trace is invariant under the ACTUAL pullback along a scheme isomorphism,
including semilinear isomorphisms: it is normalized by Kummer boundary and
the degree of divisors. No k-linear over-category isomorphism is required. -/
theorem projective_iso
    (e : D.left ≅ C.left)
    [∀ F : C.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallEtalePullback e.hom).op.HasLeftKanExtension F]
    (x : (Sheaf.rootsOfUnityAddSheaf (smallCommStructureSheaf .etale C.left) n).H 2) :
    etaleCohomology_rootsOfUnity_h2 D n hpos hn
      (ActualEtaleRootsPullback.rootsOfUnityH2Pullback e.hom n x) =
    etaleCohomology_rootsOfUnity_h2 C n hpos hn x := sorry

variable {U : Scheme.{u}} [hnonempty : Nonempty U]
variable (j : U ⟶ C.left) (j' : U ⟶ D.left) (f : D.left ⟶ C.left)
variable [IsOpenImmersion j] [IsOpenImmersion j'] [hproper : IsProper f]
variable (hcart : IsPullback (𝟙 U) j' j f)
variable [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}, (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}, (etaleRestriction j').op.HasLeftKanExtension F]
variable [∀ F : C.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}, (smallEtalePullback f).op.HasLeftKanExtension F]

include hnonempty hproper in
/-- The compact trace agrees under the actual proper refinement map, whose
data is exact Ext pullback followed by the extension-by-zero adjoint mate. -/
theorem compact_refinement
    (x : ((etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj
      (Sheaf.rootsOfUnityAddSheaf (smallCommStructureSheaf .etale U) n)).H 2) :
    SchemeOverField.NormalizedCurveTrace.intrinsicCompactKummerTrace D j' n hpos hn
      (ActualCompactificationChange.cohomologyMap j j' f hcart
        (Sheaf.rootsOfUnityAddSheaf (smallCommStructureSheaf .etale U) n) 2 x) =
    SchemeOverField.NormalizedCurveTrace.intrinsicCompactKummerTrace C j n hpos hn x := sorry

end ActualNormalizedTraceTransport
