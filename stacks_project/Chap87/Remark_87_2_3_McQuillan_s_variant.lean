/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalScheme.McQuillan
public import stacks_project.Chap87.Remark_87_2_3_McQuillan_s_variant_FormalScheme
public import stacks_project.Chap87.Remark_87_2_3_McQuillan_s_variant_Neighborhoods
import StacksCheckRecall

@[expose] public section

universe u

noncomputable section

open CategoryTheory AlgebraicGeometry

/- Remark 87.2.3 (McQuillan's variant) (5): the analogue of Lemma 87.2.1 gives
bijectivity on morphisms under the same source-size bound. -/
@[stacks 0AI3] #check
  (AlgebraicGeometry.McQuillan.FormalScheme.functorOfPoints_map_bijective :
    ∀ {P : ObjectProperty Scheme.{u}}, Scheme.IsSmallBoundClosed P →
      ∀ {X Y : AlgebraicGeometry.McQuillan.FormalScheme.{u}},
        (∃ S, P S ∧ X.size ≤ S.size) →
        Function.Bijective
          ((AlgebraicGeometry.McQuillan.FormalScheme.functorOfPoints P).map :
            (X ⟶ Y) →
              ((AlgebraicGeometry.McQuillan.FormalScheme.functorOfPoints P).obj X ⟶
                (AlgebraicGeometry.McQuillan.FormalScheme.functorOfPoints P).obj Y)))

/- (1): admissible and weakly admissible rings are complete, separated and linearly
topologized; a weak ideal of definition is an open ideal of topologically nilpotent elements. -/
#check (_root_.IsTopologicallyNilpotent :
  ∀ {A : Type u} [MonoidWithZero A] [TopologicalSpace A], A → Prop)

#check (TopologicalRing.Ideal.IsIdealOfDefinition :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A], Ideal A → Prop)

#check (TopologicalRing.IsAdmissibleRing :
  ∀ (A : Type u) [CommRing A] [TopologicalSpace A], Prop)

#check (TopologicalRing.Ideal.IsWeakIdealOfDefinition :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A], Ideal A → Prop)

#check (TopologicalRing.IsWeaklyAdmissibleRing :
  ∀ (A : Type u) [CommRing A] [TopologicalSpace A], Prop)

/- (2): intersecting a weak ideal of definition with any open ideal again gives a weak ideal. -/
#check (TopologicalRing.Ideal.IsWeakIdealOfDefinition.inf_of_isOpen :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A] {I J : Ideal A},
    TopologicalRing.Ideal.IsWeakIdealOfDefinition I → IsOpen (J : Set A) →
      TopologicalRing.Ideal.IsWeakIdealOfDefinition (I ⊓ J))

/- (3): weak ideals of definition form a fundamental system of neighbourhoods of zero. -/
#check (TopologicalRing.hasBasis_isWeakIdealOfDefinition :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyPreadmissibleRing A],
    (nhds (0 : A)).HasBasis
      (fun I : Ideal A ↦ TopologicalRing.Ideal.IsWeakIdealOfDefinition I)
      (fun I ↦ (I : Set A)))

/- (4): weak formal spectra give a larger category containing ordinary EGA formal schemes. -/
#check (AlgebraicGeometry.McQuillan.FormalScheme : Type (u + 1))

#check (AlgebraicGeometry.McQuillan.spf :
  ∀ (A : TopCommRingCat.{u}), TopologicalRing.IsWeaklyAdmissibleRing A →
    AlgebraicGeometry.LocallyTopologicallyRingedSpaceCat.{u})

#check (AlgebraicGeometry.McQuillan.FormalScheme.ofFormalScheme :
  AlgebraicGeometry.FormalScheme.{u} ⥤ AlgebraicGeometry.McQuillan.FormalScheme.{u})

/- (6): the analogue of Lemma 87.2.2 is the fpqc sheaf assertion, without a size bound on X. -/
#check (AlgebraicGeometry.McQuillan.FormalScheme.functorOfPoints_isSheaf_fpqc :
  ∀ {P : ObjectProperty Scheme.{u}}, Scheme.IsSmallBoundClosed P →
    ∀ X : AlgebraicGeometry.McQuillan.FormalScheme.{u},
      Presheaf.IsSheaf (P.ι.restrictedTopology Scheme.fpqcTopology)
        ((AlgebraicGeometry.McQuillan.FormalScheme.functorOfPoints P).obj X))
