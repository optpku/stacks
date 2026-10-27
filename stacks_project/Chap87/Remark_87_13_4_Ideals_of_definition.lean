/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalScheme.ChosenFppf.IdealColimit
public import ReasLib.AlgebraicGeometry.FormalScheme.Ideal.Valuation

/-!
# Remark 87.13.4 (Ideals of definition)

Ideals of definition, affine locality, fundamental systems, the valuation-ring
obstruction, and the quasi-compact scheme-thickening colimit criterion.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite IsLocalRing TopologicalRing

namespace AlgebraicGeometry.FormalScheme

/- Remark 87.13.4 (Ideals of definition): the quasi-compact colimit criterion. -/
@[stacks 0AIW] #check (AlgebraicGeometry.FormalScheme.sheafOfPoints_isDirectedColimit_iff_exists_fundamentalSystem :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    (X : FormalScheme.{u}) [CompactSpace X.carrier]
    (hsize : ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size),
    Nonempty (FundamentalSystem X) ↔
      ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v))),
        IsDirectedAlgebraicSpaceThickeningColimit D
            ((sheafOfPoints 𝒮 S).obj X) ∧
          ∀ i : Λ, ∃ Z : Scheme.{u},
            (∃ T : 𝒮.carrier, Z.size ≤ (𝒮.toScheme.obj T).size) ∧
            Nonempty
              (D.obj i ≅
                (sheafOfPoints 𝒮 S).obj (Scheme.toFormalScheme.obj Z)))

/- Ideals of definition on affine opens. -/
#check (AlgebraicGeometry.FormalScheme.isIdealOfDefinition_iff :
  ∀ {X : FormalScheme.{u}} (I : IdealSheafData X),
    IsIdealOfDefinition I ↔
      ∀ U : X.affineOpens, TopologicalRing.Ideal.IsIdealOfDefinition (I.ideal U))

/- Affine-cover locality of ideals of definition. -/
#check (AlgebraicGeometry.FormalScheme.isIdealOfDefinition_iff_affineCover :
  ∀ {X : FormalScheme.{u}}
    (I : IdealSheafData X) {ι : Type u} (𝒰 : ι → X.affineOpens)
    (hcover : ⨆ i, (𝒰 i).1 = ⊤),
    IsIdealOfDefinition I ↔
      ∀ i, TopologicalRing.Ideal.IsIdealOfDefinition (I.ideal (𝒰 i)))

/- The valuation-ring obstruction. -/
#check (AlgebraicGeometry.FormalScheme.not_isIdealOfDefinition_ofSpf_maximalIdeal :
  ∀ {A : Type u}
    [CommRing A] [IsDomain A] [ValuationRing A] [ValuativeRel A]
    [Valuation.Compatible
      ((ValuationRing.valuation A (FractionRing A)).comap
        (algebraMap A (FractionRing A)))]
    [ValuativeRel.IsRankLeOne A]
    [TopologicalSpace A] [IsTopologicalRing A] {π : A}
    (hπ : π ∈ maximalIdeal A) (hπ0 : π ≠ 0) (h_adic : IsAdic (Ideal.span {π}))
    [IsAdicComplete (Ideal.span {π}) A] (hFG : ¬ (maximalIdeal A).FG)
    (hA : IsAdmissibleRing A),
    ¬ IsIdealOfDefinition
        (IdealSheafData.ofSpf (.of A) hA (maximalIdeal A)
          (Ideal.isOpen_of_isOpen_subideal
            (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπ))
            (TopologicalRing.Ideal.isIdealOfDefinition_of_isAdic h_adic).1)))

/- Fundamental systems on affine opens. -/
#check (AlgebraicGeometry.FormalScheme.isFundamentalSystem_iff :
  ∀ {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X),
    IsFundamentalSystem I ↔
      ∀ U : X.affineOpens,
        TopologicalRing.Ideal.IsFundamentalSystemOfIdeals (fun i ↦ (I i).ideal U))

/- Affine-cover locality of directed fundamental families. -/
#check (AlgebraicGeometry.FormalScheme.isFundamentalSystem_iff_affineCover :
  ∀ {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X)
    (hne : Nonempty ι)
    (hdir : ∀ i j : ι, ∃ k : ι, ∀ U : X.affineOpens,
      (I k).ideal U ≤ (I i).ideal U ∧ (I k).ideal U ≤ (I j).ideal U)
    {κ : Type u} (𝒰 : κ → X.affineOpens)
    (hcover : ⨆ j, (𝒰 j).1 = ⊤),
    IsFundamentalSystem I ↔
      ∀ j, TopologicalRing.Ideal.IsFundamentalSystemOfIdeals (fun i ↦ (I i).ideal (𝒰 j)))

/- Eventuality for nonempty directed decreasing weak systems. -/
#check (AlgebraicGeometry.FormalScheme.eventually_isIdealOfDefinition :
  ∀ {X : FormalScheme.{u}}
    [CompactSpace X.carrier]
    (S : McQuillan.FormalScheme.FundamentalSystem (McQuillan.FormalScheme.ofFormalScheme.obj X))
    (hne : Nonempty S.ι)
    [Preorder S.ι] [IsDirected S.ι (· ≤ ·)]
    (hnest : ∀ i j, i ≤ j → ∀ U : (McQuillan.FormalScheme.ofFormalScheme.obj X).affineOpens,
      (S.ideal j).ideal U ≤ (S.ideal i).ideal U),
    ∃ i, ∀ j, i ≤ j →
      IsIdealOfDefinition (IdealSheafData.ofMcQuillan (S.ideal j)))

end AlgebraicGeometry.FormalScheme
