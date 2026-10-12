/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Definition_67_39_1_Etale
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_34_4_FiberDimensionLocus
public import stacks_project.Chap67.Lemma_67_34_7_QuasiFiniteLocus
public import stacks_project.Chap67.Lemma_67_38_10_SourceLocus
public import stacks_project.Chap100.Remark_100_9_19

/-!
# Unambiguous source opens for Lemma 100.9.18

Despite the warning in Remark 100.9.19, Lemma 100.9.18 applies unambiguously
for several triples of morphism properties of algebraic spaces. In each case
the fppf-local and smoothness hypotheses of Lemma 100.9.18 are omitted, while
cited Morphisms-of-Spaces results supply the largest-source-open existence and
base-change statements. Additional triples may be added by comparison with
Remark 40.6.3.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism property of having relative dimension at most `d`. -/
abbrev relativeDimensionLE {S : Scheme.{u}} (d : ℕ) :
    MorphismProperty (AlgebraicSpace S) :=
  fun _ _ f ↦ RelativeDimensionLE f d

/-- Unfolding `relativeDimensionLE d` recovers the class `RelativeDimensionLE`. -/
theorem relativeDimensionLE_def {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (d : ℕ) (f : X ⟶ Y) :
    relativeDimensionLE d f ↔ RelativeDimensionLE f d :=
  sorry

/-- Remark 100.9.20 (1): Lemma 100.9.18 applies with
`P = relativeDimensionLE d`, `Q = (@LocallyOfFiniteType S)`, and `R = ⊤`.
Thus a morphism `f : X ⟶ Y` of algebraic spaces which is locally of finite
type has a largest open source subspace `W` such that `W.ι ≫ f` has relative
dimension at most `d`. -/
@[stacks 06M5]
theorem exists_isLargestSourceOpen_relativeDimensionLE {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] (d : ℕ) :
    ∃ W : OpenSubspace X, IsLargestSourceOpen (relativeDimensionLE d) f W :=
  sorry

/-- The largest open source subspace on which `f` has relative dimension at most
`d` is stable under arbitrary base change. -/
theorem isLargestSourceOpen_relativeDimensionLE_pullback {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [LocallyOfFiniteType f] (d : ℕ) (W : OpenSubspace X)
    (hW : IsLargestSourceOpen (relativeDimensionLE d) f W) :
    IsLargestSourceOpen (relativeDimensionLE d) (pullback.snd f g)
      (W.inverseImage (pullback.fst f g)) :=
  sorry

/-- If `W` is a largest open source subspace on which `f` has relative dimension
at most `d`, then the points of `W` are exactly the points at which `f` has
relative dimension at most `d`. -/
theorem isLargestSourceOpen_relativeDimensionLE_pointsSet {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] (d : ℕ)
    (W : OpenSubspace X) (hW : IsLargestSourceOpen (relativeDimensionLE d) f W) :
    W.pointsSet = fiberDimensionLELocus f d :=
  sorry

/-- Remark 100.9.20 (2): Lemma 100.9.18 applies with
`P = (@LocallyQuasiFinite S)`, `Q = (@LocallyOfFiniteType S)`, and `R = ⊤`.
This is the case `d = 0` of the previous item. -/
@[stacks 06M5]
theorem exists_isLargestSourceOpen_locallyQuasiFinite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    ∃ W : OpenSubspace X, IsLargestSourceOpen (@LocallyQuasiFinite S) f W :=
  sorry

/-- The quasi-finite locus is a largest open source subspace on which `f` is
locally quasi-finite. -/
theorem isLargestSourceOpen_locallyQuasiFinite_quasiFiniteLocus
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    IsLargestSourceOpen (@LocallyQuasiFinite S) f (quasiFiniteLocus f) :=
  sorry

/-- The largest open source subspace on which `f` is locally quasi-finite is
stable under arbitrary base change. -/
theorem isLargestSourceOpen_locallyQuasiFinite_pullback {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [LocallyOfFiniteType f] (W : OpenSubspace X)
    (hW : IsLargestSourceOpen (@LocallyQuasiFinite S) f W) :
    IsLargestSourceOpen (@LocallyQuasiFinite S) (pullback.snd f g)
      (W.inverseImage (pullback.fst f g)) :=
  sorry

/-- Under the locally-of-finite-type hypothesis, a largest source open for
locally quasi-finite morphisms is the same as a largest source open for
relative dimension at most `0`. -/
theorem isLargestSourceOpen_locallyQuasiFinite_iff_relativeDimensionLE_zero
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (W : OpenSubspace X) :
    IsLargestSourceOpen (@LocallyQuasiFinite S) f W ↔
      IsLargestSourceOpen (relativeDimensionLE 0) f W :=
  sorry

/-- Remark 100.9.20 (3): Lemma 100.9.18 applies with `P = (@Unramified S)`,
`Q = (@LocallyOfFiniteType S)`, and `R = ⊤`. -/
@[stacks 06M5]
theorem exists_isLargestSourceOpen_unramified {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    ∃ W : OpenSubspace X, IsLargestSourceOpen (@Unramified S) f W :=
  sorry

/-- The unramified source locus is a largest open source subspace on which `f`
is unramified. -/
theorem isLargestSourceOpen_unramified_sourceLocus {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    IsLargestSourceOpen (@Unramified S) f (Unramified.sourceLocus f) :=
  sorry

/-- The largest open source subspace on which `f` is unramified is stable under
arbitrary base change. -/
theorem isLargestSourceOpen_unramified_pullback {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [LocallyOfFiniteType f] (W : OpenSubspace X)
    (hW : IsLargestSourceOpen (@Unramified S) f W) :
    IsLargestSourceOpen (@Unramified S) (pullback.snd f g)
      (W.inverseImage (pullback.fst f g)) :=
  sorry

/-- If `W` is a largest open source subspace on which `f` is unramified, then
the points of `W` are exactly the points at which `f` is unramified. -/
theorem isLargestSourceOpen_unramified_pointsSet {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (W : OpenSubspace X) (hW : IsLargestSourceOpen (@Unramified S) f W) :
    W.pointsSet = {x | UnramifiedAt f x} :=
  sorry

/-- Remark 100.9.20 (4): Lemma 100.9.18 applies with `P = (@Flat S)`,
`Q = (@LocallyOfFinitePresentation S)`, and
`R = (@Flat S ⊓ @LocallyOfFinitePresentation S)`. If `f` is locally of finite
presentation, then there is a largest open source subspace `W` on which `f` is
flat, and the points of `W` are exactly the points at which `f` is flat. -/
@[stacks 06M5]
theorem exists_isLargestSourceOpen_flat_of_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] :
    ∃ W : OpenSubspace X,
      IsLargestSourceOpen (@Flat S) f W ∧ W.pointsSet = {x | FlatAt f x} :=
  sorry

/-- Remark 100.9.20 (5): Lemma 100.9.18 applies with `P = (@Etale S)`,
`Q = (@LocallyOfFinitePresentation S)`, and
`R = (@Flat S ⊓ @LocallyOfFinitePresentation S)`. This combines (3) and (4),
since an unramified morphism which is flat and locally of finite presentation
is étale. -/
@[stacks 06M5]
theorem exists_isLargestSourceOpen_etale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    ∃ W : OpenSubspace X, IsLargestSourceOpen (@Etale S) f W :=
  sorry

/-- The largest open source subspace on which `f` is étale is stable under base
change along morphisms that are flat and locally of finite presentation. -/
theorem isLargestSourceOpen_etale_pullback {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [LocallyOfFinitePresentation f] [Flat g] [LocallyOfFinitePresentation g]
    (W : OpenSubspace X) (hW : IsLargestSourceOpen (@Etale S) f W) :
    IsLargestSourceOpen (@Etale S) (pullback.snd f g)
      (W.inverseImage (pullback.fst f g)) :=
  sorry

/-- If `W` is a largest open source subspace on which `f` is étale, then the
points of `W` are exactly the points at which `f` is étale. -/
theorem isLargestSourceOpen_etale_pointsSet {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (W : OpenSubspace X) (hW : IsLargestSourceOpen (@Etale S) f W) :
    W.pointsSet = {x | EtaleAt f x} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
