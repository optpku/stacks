/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap96.Lemma_96_11_2_Pullback
public import stacks_project.Chap96.Lemma_96_12_3_Pullback
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap103.«103_15_1_1_Smooth»
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Detection of quasi-coherence on a covering of algebraic stacks

On an algebraic stack, quasi-coherence of an étale module is detected on a
jointly point-covering family of smooth morphisms, and quasi-coherence of an
fppf module is detected on a jointly point-covering family of flat and locally
finitely presented morphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Weak sheafification of abelian groups exists on every slice of the étale
ringed site of a category fibred in groupoids. -/
instance etaleRingedSite_over_hasWeakSheafify (X : GroupoidsOver S) :
    ∀ x, HasWeakSheafify ((etaleRingedSite X).siteTopology.over x)
      AddCommGrpCat.{u} :=
  sorry

/-- On every slice of the étale ringed site of a category fibred in groupoids,
sheafification equivalences are the locally bijective morphisms. -/
instance etaleRingedSite_over_wEqualsLocallyBijective (X : GroupoidsOver S) :
    ∀ x, ((etaleRingedSite X).siteTopology.over x).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  sorry

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- Lemma 103.16.1 (1): let `X` be an algebraic stack. Let `f j : Xj j ⟶ X` be a
family of smooth morphisms of algebraic stacks with
`|X| = ⋃ |f j|(|Xj j|)`. Let `F` be a sheaf of `𝒪_X`-modules on `X_étale`. If
each inverse image `(moduleInverseImage (f j)).obj F` is quasi-coherent, then so
is `F`. -/
@[stacks 07AZ]
theorem isQuasicoherent_of_smoothCovering
    {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
    (f : ∀ j, Xj j ⟶ X) [∀ j, Smooth (f j)]
    (h_cover : ∀ x : Points X, ∃ j, x ∈ Set.range (Points.map (f j)))
    (F : etaleModules X)
    (h_qc : ∀ j, ((moduleInverseImage (f j)).obj F).IsQuasicoherent) :
    F.IsQuasicoherent :=
  sorry

/-- Lemma 103.16.1 (2): let `X` be an algebraic stack. Let `f j : Xj j ⟶ X` be a
family of flat and locally finitely presented morphisms of algebraic stacks with
`|X| = ⋃ |f j|(|Xj j|)`. Let `F` be a sheaf of `𝒪_X`-modules on `X_fppf`. If
each inverse image `(modulePullback (f j)).obj F` is quasi-coherent, then so
is `F`. -/
@[stacks 07AZ]
theorem isQuasicoherent_of_flat_locallyOfFinitePresentationCovering
    {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
    (f : ∀ j, Xj j ⟶ X) [∀ j, Flat (f j)]
    [∀ j, LocallyOfFinitePresentation (f j)]
    (h_cover : ∀ x : Points X, ∃ j, x ∈ Set.range (Points.map (f j)))
    (F : SheafOfModules.{u} (structureSheaf X))
    (h_qc : ∀ j, ((modulePullback (f j)).obj F).IsQuasicoherent) :
    F.IsQuasicoherent :=
  sorry

end AlgebraicGeometry.AlgebraicStack
