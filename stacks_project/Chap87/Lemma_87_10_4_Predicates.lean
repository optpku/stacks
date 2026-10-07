module

public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.Topology.Algebra.LinearTopology
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
public import stacks_project.Chap87.Definition_87_23_2_AdicStar
public import stacks_project.Chap87.Lemma_87_9_6_Predicates

/-!
# Sequential Spf presentations of countably indexed affine formal algebraic spaces

Named predicates for the equivalent Spf clauses of Stacks tag 0AN1: a weakly
admissible ring with countably generated neighbourhoods of `0`, a nested
countable fundamental system of weak ideals of definition, a complete linearly
topologized ring with locally nilpotent successive quotients, and a sequential
quotient inverse system `B ⧸ J n`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.IsAffineFormalAlgebraicSpace

/-- An `ℕ`-indexed diagram presents a sheaf as `Spf(A)` for a nested countable
fundamental system of weak ideals of definition: each `I n` is a weak ideal of
definition, `I (n + 1) ≤ I n`, the diagram is an `ℕ`-indexed directed affine
thickening colimit, bonding maps are `Spec` of `Ideal.Quotient.factor`, and
`{I n}` is a neighbourhood basis of `0`. -/
def IsWeakIdealSequencePresentation {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    (I : ℕ → Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
      Spec (CommRingCat.of (A ⧸ I n))) : Prop :=
  (∀ n, TopologicalRing.Ideal.IsWeakIdealOfDefinition (I n)) ∧
    (∀ n, I (n + 1) ≤ I n) ∧
      IsNatDirectedAffineThickeningColimit D X ∧
        (∀ {i j : ℕ} (f : i ⟶ j) (hI : I j ≤ I i),
          CommSq ((𝒮.bigAffineToScheme S).map (D.map f)) (e i).hom (e j).hom
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hI)))) ∧
          (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set A))

/-- A weak-ideal sequence presentation unpacks as nested weak ideals of
definition, an `ℕ`-indexed directed affine thickening colimit, commuting
quotient squares on stages, and a countable neighbourhood basis of `0`. -/
theorem isWeakIdealSequencePresentation_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    (I : ℕ → Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
      Spec (CommRingCat.of (A ⧸ I n))) :
    IsWeakIdealSequencePresentation I D X e ↔
      (∀ n, TopologicalRing.Ideal.IsWeakIdealOfDefinition (I n)) ∧
        (∀ n, I (n + 1) ≤ I n) ∧
          IsNatDirectedAffineThickeningColimit D X ∧
            (∀ {i j : ℕ} (f : i ⟶ j) (hI : I j ≤ I i),
              CommSq ((𝒮.bigAffineToScheme S).map (D.map f)) (e i).hom
                (e j).hom
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hI)))) ∧
              (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True)
                (fun n ↦ (I n : Set A)) :=
  sorry

/-- A weak-ideal sequence presentation is an `ℕ`-indexed directed affine
thickening colimit. -/
theorem IsWeakIdealSequencePresentation.isNatDirectedAffineThickeningColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : ℕ → Ideal A} {D : ℕ ⥤ 𝒮.bigAffineSite S}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
      Spec (CommRingCat.of (A ⧸ I n))}
    (h : IsWeakIdealSequencePresentation I D X e) :
    IsNatDirectedAffineThickeningColimit D X :=
  sorry

/-- A weak-ideal sequence presentation uses `{I n}` as a neighbourhood basis of
`0`, so the colimit is `Spf(A)` rather than an arbitrary subdiagram. -/
theorem IsWeakIdealSequencePresentation.isNeighborhoodBasis
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {I : ℕ → Ideal A} {D : ℕ ⥤ 𝒮.bigAffineSite S}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
      Spec (CommRingCat.of (A ⧸ I n))}
    (h : IsWeakIdealSequencePresentation I D X e) :
    (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (I n : Set A)) :=
  sorry

/-- An `ℕ`-indexed diagram presents a sheaf as `Spf(A)` for a complete separated
linearly topologized ring whose nested open ideals form a neighbourhood basis
of `0` with locally nilpotent successive quotients `I n / I (n + 1)`. This does
not assume that `A` is weakly admissible. -/
def IsLocallyNilpotentIdealSequencePresentation {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (I : ℕ → Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
      Spec (CommRingCat.of (A ⧸ I n))) : Prop :=
  T2Space A ∧
    @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) ∧
      (∀ n, IsOpen (I n : Set A)) ∧
        (∀ n, I (n + 1) ≤ I n) ∧
          (∀ n, ((I n).map (Ideal.Quotient.mk (I (n + 1)))).IsLocallyNilpotent) ∧
            IsNatDirectedAffineThickeningColimit D X ∧
              (∀ {i j : ℕ} (f : i ⟶ j) (hI : I j ≤ I i),
                CommSq ((𝒮.bigAffineToScheme S).map (D.map f)) (e i).hom
                  (e j).hom
                  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hI)))) ∧
                (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True)
                  (fun n ↦ (I n : Set A))

/-- A locally nilpotent ideal-sequence presentation unpacks as a complete
separated linearly topologized ring, nested open ideals with locally nilpotent
successive quotients, an `ℕ`-indexed directed affine thickening colimit,
commuting quotient squares, and a neighbourhood basis of `0`. -/
theorem isLocallyNilpotentIdealSequencePresentation_iff
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (I : ℕ → Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
      Spec (CommRingCat.of (A ⧸ I n))) :
    IsLocallyNilpotentIdealSequencePresentation I D X e ↔
      T2Space A ∧
        @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) ∧
          (∀ n, IsOpen (I n : Set A)) ∧
            (∀ n, I (n + 1) ≤ I n) ∧
              (∀ n,
                  ((I n).map (Ideal.Quotient.mk (I (n + 1)))).IsLocallyNilpotent) ∧
                IsNatDirectedAffineThickeningColimit D X ∧
                  (∀ {i j : ℕ} (f : i ⟶ j) (hI : I j ≤ I i),
                    CommSq ((𝒮.bigAffineToScheme S).map (D.map f)) (e i).hom
                      (e j).hom
                      (Spec.map
                        (CommRingCat.ofHom (Ideal.Quotient.factor hI)))) ∧
                    (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True)
                      (fun n ↦ (I n : Set A)) :=
  sorry

/-- A locally nilpotent ideal-sequence presentation is an `ℕ`-indexed directed
affine thickening colimit. -/
theorem IsLocallyNilpotentIdealSequencePresentation.isNatDirectedAffineThickeningColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    {I : ℕ → Ideal A} {D : ℕ ⥤ 𝒮.bigAffineSite S}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
      Spec (CommRingCat.of (A ⧸ I n))}
    (h : IsLocallyNilpotentIdealSequencePresentation I D X e) :
    IsNatDirectedAffineThickeningColimit D X :=
  sorry

/-- Successive quotients `I n / I (n + 1)` in a locally nilpotent
ideal-sequence presentation are locally nilpotent. -/
theorem IsLocallyNilpotentIdealSequencePresentation.successiveQuotient_isLocallyNilpotent
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    {I : ℕ → Ideal A} {D : ℕ ⥤ 𝒮.bigAffineSite S}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
      Spec (CommRingCat.of (A ⧸ I n))}
    (h : IsLocallyNilpotentIdealSequencePresentation I D X e) (n : ℕ) :
    ((I n).map (Ideal.Quotient.mk (I (n + 1)))).IsLocallyNilpotent :=
  sorry

/-- `X` is the sheaf colimit of `Spec(A ⧸ I)` as `I` runs over all weak ideals
of definition of a weakly admissible topological `S`-algebra `A` whose
neighbourhood filter of `0` is countably generated. This is the chosen-site
form of `X ≅ Spf(A)`. -/
def isColimitOfCountablyGeneratedSpf {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
    (_ : TopologicalRing.IsWeaklyAdmissibleRing A)
    (structureHom : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
    (D : WeakIdealOfDefinition A ⥤ 𝒮.bigAffineSite S)
    (e : ∀ I, (𝒮.bigAffineToScheme S).obj (D.obj I) ≅
      (stage A structureHom I).left),
    (∀ {I J : WeakIdealOfDefinition A} (f : I ⟶ J),
        (e I).hom ≫ ((thickenings A structureHom).map f).left =
          (𝒮.bigAffineToScheme S).map (D.map f) ≫ (e J).hom) ∧
      (∀ {I J : WeakIdealOfDefinition A} (f : I ⟶ J),
        IsThickening ((𝒮.bigAffineToScheme S).map (D.map f))) ∧
        (∃ (c : Cocone
            (D ⋙ 𝒮.bigAffineInclusion S ⋙
              (𝒮.bigTopology S).sheafifiedRepresentableFunctor)),
          Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt)) ∧
          (nhds (0 : A)).IsCountablyGenerated

/-- Unfold `isColimitOfCountablyGeneratedSpf` as a weakly admissible
`S`-algebra with countably generated neighbourhoods of `0` whose weak-ideal
spectrum realises `X` as `Spf(A)`. -/
theorem isColimitOfCountablyGeneratedSpf_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    isColimitOfCountablyGeneratedSpf X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsWeaklyAdmissibleRing A)
        (structureHom : Spec (.of A) ⟶ 𝒮.toScheme.obj S)
        (D : WeakIdealOfDefinition A ⥤ 𝒮.bigAffineSite S)
        (e : ∀ I, (𝒮.bigAffineToScheme S).obj (D.obj I) ≅
          (stage A structureHom I).left),
        (∀ {I J : WeakIdealOfDefinition A} (f : I ⟶ J),
            (e I).hom ≫ ((thickenings A structureHom).map f).left =
              (𝒮.bigAffineToScheme S).map (D.map f) ≫ (e J).hom) ∧
          (∀ {I J : WeakIdealOfDefinition A} (f : I ⟶ J),
            IsThickening ((𝒮.bigAffineToScheme S).map (D.map f))) ∧
            (∃ (c : Cocone
                (D ⋙ 𝒮.bigAffineInclusion S ⋙
                  (𝒮.bigTopology S).sheafifiedRepresentableFunctor)),
              Nonempty (IsColimit c) ∧ Nonempty (X ≅ c.pt)) ∧
              (nhds (0 : A)).IsCountablyGenerated :=
  sorry

/-- `X` is `Spf(A)` for a weakly admissible topological `S`-algebra admitting a
nested countable fundamental system of weak ideals of definition. -/
def isColimitOfWeakIdealSequence {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
    (_ : TopologicalRing.IsWeaklyAdmissibleRing A)
    (I : ℕ → Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
    (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
      Spec (CommRingCat.of (A ⧸ I n))),
    Nonempty (Spec (.of A) ⟶ 𝒮.toScheme.obj S) ∧
      IsWeakIdealSequencePresentation I D X e

/-- Unfold `isColimitOfWeakIdealSequence` as a weakly admissible `S`-algebra
together with a nested countable weak-ideal sequence presentation of `X`. -/
theorem isColimitOfWeakIdealSequence_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    isColimitOfWeakIdealSequence X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsWeaklyAdmissibleRing A)
        (I : ℕ → Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
        (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
          Spec (CommRingCat.of (A ⧸ I n))),
        Nonempty (Spec (.of A) ⟶ 𝒮.toScheme.obj S) ∧
          IsWeakIdealSequencePresentation I D X e :=
  sorry

/-- `X` is `Spf(A)` for a complete separated linearly topologized `S`-algebra
with a nested countable open neighbourhood basis of `0` whose successive
quotients are locally nilpotent. This does not assume weak admissibility. -/
def isColimitOfCompleteLocallyNilpotentSequence {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
    (_ : IsTopologicalRing A) (_ : IsLinearTopology A A)
    (I : ℕ → Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
    (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
      Spec (CommRingCat.of (A ⧸ I n))),
    Nonempty (Spec (.of A) ⟶ 𝒮.toScheme.obj S) ∧
      IsLocallyNilpotentIdealSequencePresentation I D X e

/-- Unfold `isColimitOfCompleteLocallyNilpotentSequence` as a complete linearly
topologized `S`-algebra together with a locally nilpotent nested open-ideal
presentation of `X`. -/
theorem isColimitOfCompleteLocallyNilpotentSequence_iff
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    isColimitOfCompleteLocallyNilpotentSequence X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : IsTopologicalRing A) (_ : IsLinearTopology A A)
        (I : ℕ → Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
        (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
          Spec (CommRingCat.of (A ⧸ I n))),
        Nonempty (Spec (.of A) ⟶ 𝒮.toScheme.obj S) ∧
          IsLocallyNilpotentIdealSequencePresentation I D X e :=
  sorry

/-- `X` is the sheaf colimit of `Spec(B ⧸ J n)` for nested ideals in an
`S`-algebra `B` with locally nilpotent successive quotients. This is the
chosen-site form of `X ≅ Spf(lim B ⧸ J n)` with the limit topology, without a
public inverse-limit subtype. -/
def isColimitOfQuotientInverseLimit {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop :=
  ∃ (B : Type u) (_ : CommRing B)
    (J : ℕ → Ideal B) (D : ℕ ⥤ 𝒮.bigAffineSite S)
    (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
      Spec (CommRingCat.of (B ⧸ J n))),
    Nonempty (Spec (.of B) ⟶ 𝒮.toScheme.obj S) ∧
      (∀ n, J (n + 1) ≤ J n) ∧
      (∀ n, ((J n).map (Ideal.Quotient.mk (J (n + 1)))).IsLocallyNilpotent) ∧
        IsNatDirectedAffineThickeningColimit D X ∧
          ∀ {i j : ℕ} (f : i ⟶ j) (hJ : J j ≤ J i),
            CommSq ((𝒮.bigAffineToScheme S).map (D.map f)) (e i).hom (e j).hom
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJ)))

/-- Unfold `isColimitOfQuotientInverseLimit` as an `S`-algebra `B` with a nested
sequence of ideals whose successive quotients are locally nilpotent and whose
`Spec(B ⧸ J n)` stages realise `X`. -/
theorem isColimitOfQuotientInverseLimit_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    isColimitOfQuotientInverseLimit X ↔
      ∃ (B : Type u) (_ : CommRing B)
        (J : ℕ → Ideal B) (D : ℕ ⥤ 𝒮.bigAffineSite S)
        (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
          Spec (CommRingCat.of (B ⧸ J n))),
        Nonempty (Spec (.of B) ⟶ 𝒮.toScheme.obj S) ∧
          (∀ n, J (n + 1) ≤ J n) ∧
          (∀ n, ((J n).map (Ideal.Quotient.mk (J (n + 1)))).IsLocallyNilpotent) ∧
            IsNatDirectedAffineThickeningColimit D X ∧
              ∀ {i j : ℕ} (f : i ⟶ j) (hJ : J j ≤ J i),
                CommSq ((𝒮.bigAffineToScheme S).map (D.map f)) (e i).hom
                  (e j).hom
                  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJ))) :=
  sorry

end AlgebraicGeometry.IsAffineFormalAlgebraicSpace
