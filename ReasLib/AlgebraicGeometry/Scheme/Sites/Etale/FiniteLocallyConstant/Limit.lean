/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Limit

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Etale.FiniteLocallyConstant

/-- Finite locally constant set-valued sheaves satisfy filtered categorical descent along
a directed inverse limit of quasi-compact, quasi-separated schemes with affine transitions. -/
theorem setHasFilteredDescent
    {I : Type u} [Preorder I] (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D)
    [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
    [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
    [∀ S : Scheme.{u}, HasWeakSheafify S.smallEtaleTopology (Type (u + 1))]
    [∀ (S : Scheme.{u}) (U : S.Etale),
      HasWeakSheafify (S.smallEtaleTopology.over U) (Type (u + 1))]
    [∀ (S T : Scheme.{u}) (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ Type (u + 1)),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
    (hc : IsLimit c) :
    AlgebraicGeometry.Scheme.Etale.Constructible.HasFilteredDescent
      (A := Type (u + 1)) D c (fun _ F ↦ CategoryTheory.Sheaf.IsFiniteLocallyConstant F) := sorry

/-- Finite locally constant abelian sheaves satisfy filtered categorical descent along
a directed inverse limit of quasi-compact, quasi-separated schemes with affine transitions. -/
theorem addCommGrpHasFilteredDescent
    {I : Type u} [Preorder I] (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D)
    [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
    [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
    [∀ S : Scheme.{u}, HasWeakSheafify S.smallEtaleTopology (AddCommGrpCat.{u + 1})]
    [∀ (S : Scheme.{u}) (U : S.Etale),
      HasWeakSheafify (S.smallEtaleTopology.over U) (AddCommGrpCat.{u + 1})]
    [∀ (S T : Scheme.{u}) (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
    (hc : IsLimit c) :
    AlgebraicGeometry.Scheme.Etale.Constructible.HasFilteredDescent
      (A := AddCommGrpCat.{u + 1}) D c (fun _ F ↦ CategoryTheory.Sheaf.IsFiniteLocallyConstantAddCommGrp F) := sorry

/-- Locally constant sheaves of finite-type modules over a Noetherian ring satisfy filtered
categorical descent along a directed inverse limit of quasi-compact, quasi-separated schemes
with affine transitions. -/
theorem moduleHasFilteredDescent
    {I : Type u} [Preorder I] (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D)
    {Λ : Type v} [Ring Λ] [IsNoetherianRing Λ]
    [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
    [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
    [∀ S : Scheme.{u}, HasWeakSheafify S.smallEtaleTopology (ModuleCat.{v} Λ)]
    [∀ (S : Scheme.{u}) (U : S.Etale),
      HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
    [∀ (S T : Scheme.{u}) (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
    (hc : IsLimit c) :
    AlgebraicGeometry.Scheme.Etale.Constructible.HasFilteredDescent
      (A := ModuleCat.{v} Λ) D c (fun _ F ↦ CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule F) := sorry

end AlgebraicGeometry.Scheme.Etale.FiniteLocallyConstant
