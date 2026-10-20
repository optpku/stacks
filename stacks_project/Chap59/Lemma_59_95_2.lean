/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CohomologicalDimension.InverseLimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 59.95.2: if `X = lim X_i` is a directed inverse limit of quasi-compact
quasi-separated schemes with affine transition morphisms, then
`cohomologicalDimension X ≤ ⨆ i, cohomologicalDimension (X_i)`. Here `X` is the
apex `c.pt` of a limit cone on `D : OrderDual I ⥤ Scheme`. -/
@[stacks 0F0R] #check (AlgebraicGeometry.Scheme.cohomologicalDimension_le_iSup_of_isLimit :
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u})
    [∀ {i j : I} (hij : i ≤ j), IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
    [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
    [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
    [∀ i : I, HasExt.{u} (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
    (c : Cone D) [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})] (hc : IsLimit c),
      Scheme.cohomologicalDimension c.pt ≤
        ⨆ i : I, Scheme.cohomologicalDimension (D.obj (OrderDual.toDual i)))

/- The corresponding vanishing bound for every locally torsion abelian sheaf. -/
#check (AlgebraicGeometry.Scheme.cohomologicalDimensionBound_of_iSup_of_isLimit :
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u})
    [∀ {i j : I} (hij : i ≤ j), IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
    [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
    [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
    [∀ i : I, HasExt.{u} (Sheaf (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
    (c : Cone D) [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})] (hc : IsLimit c),
      Scheme.cohomologicalDimensionBound c.pt
        (⨆ i : I, Scheme.cohomologicalDimension (D.obj (OrderDual.toDual i))))

end
