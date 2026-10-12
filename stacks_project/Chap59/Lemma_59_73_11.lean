/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_73_11_Diagram
public import Mathlib.CategoryTheory.Category.Cat

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale.FiniteLocallyConstant

noncomputable section

universe u v w

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ {i j : I} (hij : i ≤ j),
    IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
variable [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
variable [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
variable (c : Cone D)

/-- Lemma 59.73.11 (1): for a directed inverse limit of qcqs schemes with affine transition
morphisms, the category of finite locally constant sheaves of sets on the small étale
site of the limit is the filtered colimit of the corresponding categories on the stages,
via inverse image along the cone projections. -/
@[stacks 0GL2]
noncomputable def finiteLocallyConstantSet_isColimit
    [∀ {S : Scheme.{u}}, HasWeakSheafify S.smallEtaleTopology (Type (u + 1))]
    [∀ {S : Scheme.{u}} (U : S.Etale),
      HasWeakSheafify (S.smallEtaleTopology.over U) (Type (u + 1))]
    [∀ {S T : Scheme.{u}} (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ Type (u + 1)),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
    (hc : IsLimit c) :
    IsColimit (setCocone setProperty D c) where
  desc s := setDesc setProperty D c hc s
  fac _ _ := sorry
  uniq _ _ _ := sorry

/-- Factorization identities for the mediating morphisms of
`finiteLocallyConstantSet_isColimit`. -/
theorem finiteLocallyConstantSet_isColimit_fac
    [∀ {S : Scheme.{u}}, HasWeakSheafify S.smallEtaleTopology (Type (u + 1))]
    [∀ {S : Scheme.{u}} (U : S.Etale),
      HasWeakSheafify (S.smallEtaleTopology.over U) (Type (u + 1))]
    [∀ {S T : Scheme.{u}} (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ Type (u + 1)),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
    (hc : IsLimit c)
    (s : Cocone (setDiagram setProperty D)) (j : I) :
    (setCocone setProperty D c).ι.app j ≫
      (finiteLocallyConstantSet_isColimit D c hc).desc s =
      s.ι.app j :=
  sorry

/-- Under a chosen colimit of the finite locally constant set diagram, the comparison
functor is an equivalence. -/
theorem finiteLocallyConstantSet_colimit_equivalence
    [∀ {S : Scheme.{u}}, HasWeakSheafify S.smallEtaleTopology (Type (u + 1))]
    [∀ {S : Scheme.{u}} (U : S.Etale),
      HasWeakSheafify (S.smallEtaleTopology.over U) (Type (u + 1))]
    [∀ {S T : Scheme.{u}} (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ Type (u + 1)),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
    [HasColimit (setDiagram setProperty D)]
    (hc : IsLimit c) :
    (setComparison setProperty D c).toFunctor.IsEquivalence :=
  sorry

/-- Lemma 59.73.11 (2): for a directed inverse limit of qcqs schemes with affine transition
morphisms, the category of finite locally constant abelian sheaves on the small étale
site of the limit is the filtered colimit of the corresponding categories on the stages. -/
@[stacks 0GL2]
noncomputable def finiteLocallyConstantAddCommGrp_isColimit
    [∀ {S : Scheme.{u}}, HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ {S : Scheme.{u}} (U : S.Etale),
      HasWeakSheafify (S.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [∀ {S T : Scheme.{u}} (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
    (hc : IsLimit c) :
    IsColimit (addCommGrpCocone addCommGrpProperty D c) where
  desc s := addCommGrpDesc addCommGrpProperty D c hc s
  fac _ _ := sorry
  uniq _ _ _ := sorry

/-- Factorization identities for the mediating morphisms of
`finiteLocallyConstantAddCommGrp_isColimit`. -/
theorem finiteLocallyConstantAddCommGrp_isColimit_fac
    [∀ {S : Scheme.{u}}, HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ {S : Scheme.{u}} (U : S.Etale),
      HasWeakSheafify (S.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [∀ {S T : Scheme.{u}} (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
    (hc : IsLimit c)
    (s : Cocone (addCommGrpDiagram addCommGrpProperty D)) (j : I) :
    (addCommGrpCocone addCommGrpProperty D c).ι.app j ≫
      (finiteLocallyConstantAddCommGrp_isColimit D c hc).desc s =
      s.ι.app j :=
  sorry

/-- Under a chosen colimit of the finite locally constant abelian diagram, the comparison
functor is an equivalence. -/
theorem finiteLocallyConstantAddCommGrp_colimit_equivalence
    [∀ {S : Scheme.{u}}, HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ {S : Scheme.{u}} (U : S.Etale),
      HasWeakSheafify (S.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [∀ {S T : Scheme.{u}} (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
    [HasColimit (addCommGrpDiagram addCommGrpProperty D)]
    (hc : IsLimit c) :
    (addCommGrpComparison addCommGrpProperty D c).toFunctor.IsEquivalence :=
  sorry

/-- Lemma 59.73.11 (3): for a Noetherian ring `Λ` and a directed inverse limit of qcqs
schemes with affine transition morphisms, the category of finite type, locally constant
sheaves of `Λ`-modules on the small étale site of the limit is the filtered colimit of
the corresponding categories on the stages. -/
@[stacks 0GL2]
noncomputable def finiteTypeLocallyConstantModule_isColimit
    {Λ : Type v} [Ring Λ] [IsNoetherianRing Λ]
    [∀ {S : Scheme.{u}}, HasWeakSheafify S.smallEtaleTopology (ModuleCat.{v} Λ)]
    [∀ {S : Scheme.{u}} (U : S.Etale),
      HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
    [∀ {S T : Scheme.{u}} (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
    (hc : IsLimit c) :
    IsColimit (cocone (moduleProperty Λ) D c) where
  desc s := desc (moduleProperty Λ) D c hc s
  fac _ _ := sorry
  uniq _ _ _ := sorry

/-- Factorization identities for the mediating morphisms of
`finiteTypeLocallyConstantModule_isColimit`. -/
theorem finiteTypeLocallyConstantModule_isColimit_fac
    {Λ : Type v} [Ring Λ] [IsNoetherianRing Λ]
    [∀ {S : Scheme.{u}}, HasWeakSheafify S.smallEtaleTopology (ModuleCat.{v} Λ)]
    [∀ {S : Scheme.{u}} (U : S.Etale),
      HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
    [∀ {S T : Scheme.{u}} (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
    (hc : IsLimit c)
    (s : Cocone (diagram (moduleProperty Λ) D)) (j : I) :
    (cocone (moduleProperty Λ) D c).ι.app j ≫
      (finiteTypeLocallyConstantModule_isColimit D c hc).desc s =
      s.ι.app j :=
  sorry

/-- Under a chosen colimit of the finite-type locally constant module diagram, the
comparison functor is an equivalence. -/
theorem finiteTypeLocallyConstantModule_colimit_equivalence
    {Λ : Type v} [Ring Λ] [IsNoetherianRing Λ]
    [∀ {S : Scheme.{u}}, HasWeakSheafify S.smallEtaleTopology (ModuleCat.{v} Λ)]
    [∀ {S : Scheme.{u}} (U : S.Etale),
      HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
    [∀ {S T : Scheme.{u}} (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
    [HasColimit (diagram (moduleProperty Λ) D)]
    (hc : IsLimit c) :
    (comparison (moduleProperty Λ) D c).toFunctor.IsEquivalence :=
  sorry

end
