/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import stacks_project.Chap03.Lemma_3_9_2_ObjectProperty
public import stacks_project.Chap87.Lemma_87_18_1_Colimit
public import stacks_project.Chap87.Remark_87_13_4_Ideals_of_definition_Comparison
public import stacks_project.Chap87.Remark_87_13_4_Ideals_of_definition_Ideal
public import stacks_project.Chap87.Remark_87_13_4_Ideals_of_definition_System

/-!
# Remark 87.13.4 (Ideals of definition)

Ideals of definition on an EGA formal scheme, fundamental systems of those
ideal sheaves, the failure of the thickening correspondence of
Remark 87.13.3, and the quasi-compact colimit criterion.
-/

@[expose] public section

universe u v

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite IsLocalRing
open TopologicalRing
open McQuillan.FormalScheme (ofFormalScheme)

namespace AlgebraicGeometry.FormalScheme

/-- Remark 87.13.4 (Ideals of definition) (1): an ideal sheaf on an EGA formal
scheme `X` is an ideal of definition iff for every affine formal open `U` the
ideal of sections is an ideal of definition of the admissible ring
`X.presheaf.obj (op U)`. -/
@[stacks 0AIW]
theorem isIdealOfDefinition_affineOpens {X : FormalScheme.{u}}
    (I : IdealSheafData X) :
    IsIdealOfDefinition I ↔
      ∀ U : X.affineOpens,
        TopologicalRing.Ideal.IsIdealOfDefinition (I.ideal U) :=
  sorry

/-- Remark 87.13.4 (Ideals of definition) (2): the ideal-of-definition condition
on an ideal sheaf may be checked on the members of an affine open covering. -/
@[stacks 0AIW]
theorem isIdealOfDefinition_affineCover {X : FormalScheme.{u}}
    (I : IdealSheafData X) {ι : Type u} (𝒰 : ι → X.affineOpens)
    (hcover : ⨆ i, (𝒰 i).1 = ⊤) :
    IsIdealOfDefinition I ↔
      ∀ i, TopologicalRing.Ideal.IsIdealOfDefinition (I.ideal (𝒰 i)) :=
  sorry

/-- Remark 87.13.4 (Ideals of definition) (3): unlike Remark 87.13.3, ideals of
definition are not in bijection with thickenings `Z ⟶ h_X`; in the situation
of Example 87.13.2 the maximal-ideal sheaf on `ofSpf A` is not an ideal of
definition. -/
@[stacks 0AIW]
theorem not_isIdealOfDefinition_ofSpf_maximalIdeal {A : Type u}
    [CommRing A] [IsDomain A] [ValuationRing A] [ValuativeRel A]
    [Valuation.Compatible
      ((ValuationRing.valuation A (FractionRing A)).comap
        (algebraMap A (FractionRing A)))]
    [ValuativeRel.IsRankLeOne A]
    [TopologicalSpace A] [IsTopologicalRing A] {π : A}
    (hπ : π ∈ maximalIdeal A) (hπ0 : π ≠ 0) (h_adic : IsAdic (Ideal.span {π}))
    [IsAdicComplete (Ideal.span {π}) A] (hFG : ¬ (maximalIdeal A).FG)
    (hA : IsAdmissibleRing A) :
    ¬ IsIdealOfDefinition
        (IdealSheafData.ofSpf (.of A) hA (maximalIdeal A)) :=
  sorry

/-- Remark 87.13.4 (Ideals of definition) (4): a family of ideal sheaves is a
fundamental system of ideals of definition iff on every affine formal open the
section ideals form a fundamental system of ideals of definition of the
section ring. -/
@[stacks 0AIW]
theorem isFundamentalSystem_affineOpens {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) :
    IsFundamentalSystem I ↔
      ∀ U : X.affineOpens,
        TopologicalRing.Ideal.IsFundamentalSystemOfIdeals
          (fun i ↦ (I i).ideal U) :=
  sorry

/-- Remark 87.13.4 (Ideals of definition) (5): the fundamental-system condition
may be checked on the members of an affine open covering. -/
@[stacks 0AIW]
theorem isFundamentalSystem_affineCover {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) {κ : Type u} (𝒰 : κ → X.affineOpens)
    (hcover : ⨆ j, (𝒰 j).1 = ⊤) :
    IsFundamentalSystem I ↔
      ∀ j, TopologicalRing.Ideal.IsFundamentalSystemOfIdeals
          (fun i ↦ (I i).ideal (𝒰 j)) :=
  sorry

/-- Remark 87.13.4 (Ideals of definition) (6): if `X` is quasi-compact and `S`
is a directed nested fundamental system of weak ideals of definition on the
McQuillan embedding, then for all sufficiently large indices the members are
ideals of definition. -/
@[stacks 0AIW]
theorem eventually_isIdealOfDefinition {X : FormalScheme.{u}}
    [CompactSpace X.carrier]
    (S : McQuillan.FormalScheme.FundamentalSystem (ofFormalScheme.obj X))
    [Preorder S.ι] [IsDirected S.ι (· ≤ ·)]
    (hnest : ∀ i j, i ≤ j → ∀ U : (ofFormalScheme.obj X).affineOpens,
      (S.ideal j).ideal U ≤ (S.ideal i).ideal U) :
    ∃ i, ∀ j, i ≤ j →
      IsIdealOfDefinition (IdealSheafData.ofMcQuillan (S.ideal j)) :=
  sorry

/-- Remark 87.13.4 (Ideals of definition) (7): for a quasi-compact EGA formal
scheme `X`, the associated formal algebraic space `h_X` is a directed colimit
of schemes along thickenings as in Lemma 87.13.1 iff there exists a
fundamental system of ideals of definition for `X`. -/
@[stacks 0AIW]
theorem sheafOfPoints_isDirectedColimit_iff_exists_fundamentalSystem
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    (X : FormalScheme.{u}) [CompactSpace X.carrier]
    (hsize : ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size) :
    Nonempty (FundamentalSystem X) ↔
      ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v))),
        IsDirectedAlgebraicSpaceThickeningColimit D
            ((sheafOfPoints 𝒮 S).obj X) ∧
          ∀ i : Λ, ∃ Z : Scheme.{u},
            Nonempty
              (D.obj i ≅
                (sheafOfPoints 𝒮 S).obj (Scheme.toFormalScheme.obj Z)) :=
  sorry

end AlgebraicGeometry.FormalScheme
