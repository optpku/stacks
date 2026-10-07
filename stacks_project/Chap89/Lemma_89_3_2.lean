module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap89.«89_3_0_1»

/-!
# Transport of morphism properties across family excision

In the setup of 89.3.0.1, a morphism `f : Y ⟶ X` that is an isomorphism
over `X \ {x i}` is quasi-compact, quasi-separated, separated, locally of
finite presentation, of finite presentation, locally of finite type, of
finite type, proper, integral, or finite if and only if every corresponding
base change `g i : Y i ⟶ U i` is.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsoOverClosedPoints

/-- Lemma 89.3.2 (1): in the setup of 89.3.0.1, if `f : Y ⟶ X` corresponds
under `F` to `g i : Y i ⟶ U i`, then `f` is quasi-compact if and only if
every `g i` is. Here `F` is `excisionFamilyFunctor`, and `g i` is
`overPullbackSnd (U i).hom Y.obj`. -/
@[stacks 0BHC]
theorem quasiCompact_hom_iff {ι : Type} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) (Y : IsoOverClosedPoints X x hx) :
    QuasiCompact Y.obj.hom ↔
      ∀ i, QuasiCompact (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- Lemma 89.3.2 (2): in the setup of 89.3.0.1, if `f : Y ⟶ X` corresponds
under `F` to `g i : Y i ⟶ U i`, then `f` is quasi-separated if and only if
every `g i` is. Here `F` is `excisionFamilyFunctor`, and `g i` is
`overPullbackSnd (U i).hom Y.obj`. -/
@[stacks 0BHC]
theorem quasiSeparated_hom_iff {ι : Type} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) (Y : IsoOverClosedPoints X x hx) :
    QuasiSeparated Y.obj.hom ↔
      ∀ i, QuasiSeparated (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- Lemma 89.3.2 (3): in the setup of 89.3.0.1, if `f : Y ⟶ X` corresponds
under `F` to `g i : Y i ⟶ U i`, then `f` is separated if and only if every
`g i` is. Here `F` is `excisionFamilyFunctor`, and `g i` is
`overPullbackSnd (U i).hom Y.obj`. -/
@[stacks 0BHC]
theorem separated_hom_iff {ι : Type} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) (Y : IsoOverClosedPoints X x hx) :
    Separated Y.obj.hom ↔ ∀ i, Separated (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- Lemma 89.3.2 (4): in the setup of 89.3.0.1, if `f : Y ⟶ X` corresponds
under `F` to `g i : Y i ⟶ U i`, then `f` is locally of finite presentation
if and only if every `g i` is. Here `F` is `excisionFamilyFunctor`, and
`g i` is `overPullbackSnd (U i).hom Y.obj`. -/
@[stacks 0BHC]
theorem locallyOfFinitePresentation_hom_iff {ι : Type} [Finite ι]
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) (Y : IsoOverClosedPoints X x hx) :
    LocallyOfFinitePresentation Y.obj.hom ↔
      ∀ i, LocallyOfFinitePresentation (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- Lemma 89.3.2 (5): in the setup of 89.3.0.1, if `f : Y ⟶ X` corresponds
under `F` to `g i : Y i ⟶ U i`, then `f` is of finite presentation if and
only if every `g i` is. Here `F` is `excisionFamilyFunctor`, and `g i` is
`overPullbackSnd (U i).hom Y.obj`. -/
@[stacks 0BHC]
theorem finitePresentation_hom_iff {ι : Type} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) (Y : IsoOverClosedPoints X x hx) :
    FinitePresentation Y.obj.hom ↔
      ∀ i, FinitePresentation (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- Lemma 89.3.2 (6): in the setup of 89.3.0.1, if `f : Y ⟶ X` corresponds
under `F` to `g i : Y i ⟶ U i`, then `f` is locally of finite type if and
only if every `g i` is. Here `F` is `excisionFamilyFunctor`, and `g i` is
`overPullbackSnd (U i).hom Y.obj`. -/
@[stacks 0BHC]
theorem locallyOfFiniteType_hom_iff {ι : Type} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) (Y : IsoOverClosedPoints X x hx) :
    LocallyOfFiniteType Y.obj.hom ↔
      ∀ i, LocallyOfFiniteType (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- Lemma 89.3.2 (7): in the setup of 89.3.0.1, if `f : Y ⟶ X` corresponds
under `F` to `g i : Y i ⟶ U i`, then `f` is of finite type if and only if
every `g i` is. Here `F` is `excisionFamilyFunctor`, and `g i` is
`overPullbackSnd (U i).hom Y.obj`. -/
@[stacks 0BHC]
theorem finiteType_hom_iff {ι : Type} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) (Y : IsoOverClosedPoints X x hx) :
    FiniteType Y.obj.hom ↔ ∀ i, FiniteType (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- Lemma 89.3.2 (8): in the setup of 89.3.0.1, if `f : Y ⟶ X` corresponds
under `F` to `g i : Y i ⟶ U i`, then `f` is proper if and only if every
`g i` is. Here `F` is `excisionFamilyFunctor`, and `g i` is
`overPullbackSnd (U i).hom Y.obj`. -/
@[stacks 0BHC]
theorem proper_hom_iff {ι : Type} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) (Y : IsoOverClosedPoints X x hx) :
    Proper Y.obj.hom ↔ ∀ i, Proper (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- Lemma 89.3.2 (9): in the setup of 89.3.0.1, if `f : Y ⟶ X` corresponds
under `F` to `g i : Y i ⟶ U i`, then `f` is integral if and only if every
`g i` is. Here `F` is `excisionFamilyFunctor`, and `g i` is
`overPullbackSnd (U i).hom Y.obj`. -/
@[stacks 0BHC]
theorem isIntegralHom_hom_iff {ι : Type} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) (Y : IsoOverClosedPoints X x hx) :
    IsIntegralHom Y.obj.hom ↔
      ∀ i, IsIntegralHom (overPullbackSnd (U i).hom Y.obj) :=
  sorry

/-- Lemma 89.3.2 (10): in the setup of 89.3.0.1, if `f : Y ⟶ X` corresponds
under `F` to `g i : Y i ⟶ U i`, then `f` is finite if and only if every
`g i` is. Here `F` is `excisionFamilyFunctor`, and `g i` is
`overPullbackSnd (U i).hom Y.obj`. -/
@[stacks 0BHC]
theorem isFinite_hom_iff {ι : Type} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) (Y : IsoOverClosedPoints X x hx) :
    IsFinite Y.obj.hom ↔ ∀ i, IsFinite (overPullbackSnd (U i).hom Y.obj) :=
  sorry

end IsoOverClosedPoints

end AlgebraicGeometry.AlgebraicSpace
