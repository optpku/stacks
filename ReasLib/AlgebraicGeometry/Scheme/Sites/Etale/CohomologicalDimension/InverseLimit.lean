/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CohomologicalDimension
public import ReasLib.CategoryTheory.InverseSystem.Preorder
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {I : Type u} [Preorder I] [h_nonempty : Nonempty I]
variable [h_directed : IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [h_affine : ∀ {i j : I} (hij : i ≤ j),
    IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
variable [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
variable [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
variable [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasExt.{u} (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable (c : Cone D)
variable [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
variable [HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})]

include h_nonempty h_directed h_affine

/-- The supremum of the étale cohomological dimensions of the stages of a nonempty
directed inverse system of quasi-compact quasi-separated schemes with affine
transition morphisms is a vanishing bound for its limit. -/
theorem cohomologicalDimensionBound_of_iSup_of_isLimit (hc : IsLimit c) :
    cohomologicalDimensionBound c.pt
      (⨆ i : I, cohomologicalDimension (D.obj (OrderDual.toDual i))) := sorry

/-- The étale cohomological dimension of a nonempty directed inverse limit of
quasi-compact quasi-separated schemes with affine transition morphisms is at most
the supremum of the étale cohomological dimensions of its stages. -/
theorem cohomologicalDimension_le_iSup_of_isLimit (hc : IsLimit c) :
    cohomologicalDimension c.pt ≤
      ⨆ i : I, cohomologicalDimension (D.obj (OrderDual.toDual i)) := sorry

end AlgebraicGeometry.Scheme

end
