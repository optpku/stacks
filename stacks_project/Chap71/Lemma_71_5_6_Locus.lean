/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sets.Opens
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_2
public import stacks_project.Chap65.Lemma_65_12_3_Pullback
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap71.Lemma_71_5_1_FittingIdeal

/-!
# Fitting loci of modules on algebraic spaces

The Fitting ideals of a finite-type quasi-coherent module on an algebraic space
cut out a nested sequence of closed subspaces, together with the complementary
open subspaces and the successive locally closed rank loci.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A morphism `f : Y ⟶ X` vanishes on an ideal sheaf when the pulled-back
inclusion into `𝒪_Y` is zero. -/
def idealPullbackVanishes {Y : AlgebraicSpace S} (f : Y ⟶ X)
    (I : IdealSubobject X) : Prop :=
  I.pullbackMap f = 0

/-- Vanishing of an ideal along a test morphism is preserved by precomposition
with a morphism of test schemes. -/
theorem idealPullbackVanishes_map {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (I : IdealSubobject X) {h : X.functorOfPoints.obj T}
    (hh : idealPullbackVanishes (OpenSubspace.homOfPointsSection h) I) :
    idealPullbackVanishes
      (OpenSubspace.homOfPointsSection (X.functorOfPoints.map φ h)) I :=
  sorry

/-- Functor of points of the closed subspace cut out by a Fitting ideal: `T`-points
are morphisms `T ⟶ X` along which the pulled-back Fitting inclusion vanishes. -/
def fittingClosedSubfunctor (F : X.Modules) (r : ℕ) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T :=
    {h : X.functorOfPoints.obj T //
      idealPullbackVanishes (OpenSubspace.homOfPointsSection h)
        (fittingIdealSheaf F r)}
  map φ :=
    TypeCat.ofHom fun h ↦
      ⟨X.functorOfPoints.map φ h.val,
        idealPullbackVanishes_map φ (fittingIdealSheaf F r) h.property⟩
  map_id := sorry
  map_comp := sorry

/-- The algebraic space underlying the closed subspace cut out by the `r`th
Fitting ideal of `F`. -/
def fittingClosedSpace (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (r : ℕ) : AlgebraicSpace S :=
  ofFunctor (fittingClosedSubfunctor F r) sorry sorry sorry

/-- The closed-subspace inclusion of the locus cut out by the `r`th Fitting
ideal of `F`. -/
def fittingClosedι (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (r : ℕ) : fittingClosedSpace F r ⟶ X where
  app T := TypeCat.ofHom fun h ↦ h.val
  naturality := sorry

/-- The Fitting closed-subspace inclusion is a closed immersion. -/
instance instIsClosedImmersion_fittingClosedι (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) :
    IsClosedImmersion (fittingClosedι F r) :=
  sorry

/-- The closed subspace `Z_r` of `X` cut out by the `r`th Fitting ideal of `F`. -/
def fittingClosedSubspace (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (r : ℕ) : ClosedSubspace X :=
  ClosedSubspace.ofι (fittingClosedι F r)

/-- The inclusion of a Fitting closed subspace is a closed immersion. -/
instance instIsClosedImmersion_fittingClosedSubspace_ι
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) :
    IsClosedImmersion (fittingClosedSubspace F r).ι :=
  (fittingClosedSubspace F r).isClosedImmersion

/-- The inclusion of `fittingClosedSubspace F r` is `fittingClosedι F r`. -/
theorem fittingClosedSubspace_ι (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] (r : ℕ) :
    (fittingClosedSubspace F r).ι = fittingClosedι F r :=
  sorry

/-- The underlying point-set of `fittingClosedSubspace F r` is the image of its
inclusion on points. -/
theorem fittingClosedSubspace_pointsSet_eq_range (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) :
    (fittingClosedSubspace F r).pointsSet =
      Set.range (Points.map (fittingClosedSubspace F r).ι) :=
  sorry

/-- The Fitting closed subspaces are nested: `|Z_{r+1}| ⊆ |Z_r|`. -/
theorem fittingClosedSubspace_pointsSet_antitone (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) :
    (fittingClosedSubspace F (r + 1)).pointsSet ⊆
      (fittingClosedSubspace F r).pointsSet :=
  sorry

namespace fittingClosedSubspace

/-- The Fitting closed subspace of index `-1` is the ambient algebraic space. -/
def negOne (X : AlgebraicSpace S) : ClosedSubspace X :=
  ClosedSubspace.id X

/-- The underlying point-set of the index `-1` Fitting closed subspace is all of
`|X|`. -/
theorem negOne_pointsSet (X : AlgebraicSpace S) :
    (negOne X).pointsSet = Set.univ :=
  sorry

end fittingClosedSubspace

/-- The open subspace `X \ Z_r` complementary to the `r`th Fitting closed subspace. -/
def fittingOpenComplement (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (r : ℕ) : OpenSubspace X :=
  OpenSubspace.ofOpens
    (Opens.mk (fittingClosedSubspace F r).pointsSetᶜ
      (fittingClosedSubspace F r).isClosed_pointsSet.isOpen_compl)

/-- The inclusion of a Fitting open complement is an open immersion. -/
instance instIsOpenImmersion_fittingOpenComplement_ι (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) :
    IsOpenImmersion (fittingOpenComplement F r).ι :=
  (fittingOpenComplement F r).isOpenImmersion

/-- The underlying point-set of `fittingOpenComplement F r` is the complement of
`|Z_r|`. -/
theorem fittingOpenComplement_pointsSet (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] (r : ℕ) :
    (fittingOpenComplement F r).pointsSet =
      (fittingClosedSubspace F r).pointsSetᶜ :=
  sorry

/-- The locally closed Fitting rank locus `Z_{r-1} \ Z_r`, with `Z_{-1} = X`. -/
def fittingRankLocus (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (r : ℕ) : LocallyClosedSubspace X :=
  match r with
  | 0 => LocallyClosedSubspace.ofι (fittingOpenComplement F 0).ι
  | r + 1 =>
      LocallyClosedSubspace.ofι
        (pullback.snd (fittingOpenComplement F (r + 1)).ι
            (fittingClosedSubspace F r).ι ≫
          (fittingClosedSubspace F r).ι)

/-- The inclusion of a Fitting rank locus is an immersion. -/
instance instIsImmersion_fittingRankLocus_ι (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] (r : ℕ) : IsImmersion (fittingRankLocus F r).ι :=
  (fittingRankLocus F r).isImmersion

/-- The rank-zero Fitting locus is the open complement of `Z_0`. -/
theorem fittingRankLocus_zero (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] :
    fittingRankLocus F 0 =
      LocallyClosedSubspace.ofι (fittingOpenComplement F 0).ι :=
  sorry

/-- The successive Fitting rank locus at `r + 1` is the open-in-closed pullback of
`X \ Z_{r+1}` along `Z_r ⟶ X`. -/
theorem fittingRankLocus_succ_isPullback (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] (r : ℕ) :
    (fittingRankLocus F (r + 1)).ι =
      pullback.snd (fittingOpenComplement F (r + 1)).ι
          (fittingClosedSubspace F r).ι ≫
        (fittingClosedSubspace F r).ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
