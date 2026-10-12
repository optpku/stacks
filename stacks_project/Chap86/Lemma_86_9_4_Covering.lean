/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap86.Definition_86_9_1_RelativeDualizing

/-!
# Étale covering recognition for relative dualizing complexes

A `Y`-perfect pair `(ω, τ)` that matches the twisted-inverse pair on an étale
covering by affine algebraic spaces is a relative dualizing complex.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex

/-- After cartesian base change along a single square with affine target, the
pulled-back pair `(L(g')^* ω, Lg^* τ)` is isomorphic to the twisted-inverse pair
`(a'(𝒪_{Y'}), Tr)`. -/
def affineBaseChangeOn {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [IsAffine Y'] [QuasiCompact f'] [QuasiSeparated f']
    (sq : IsPullback g' f' f g) (ω : ModuleDerived X)
    (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y) : Prop :=
  ∀ (a' : DerivedQCoh Y' ⥤ DerivedQCoh X') (adj : pushforwardCohomologyIn f' ⊣ a')
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)],
    IsIso (baseChangeMate g' f' f g sq adj_f adj_f' ω) ∧
      ∃ e : (ModuleDerived.pullback g').obj ω ≅ twistedInverseComplex f' a',
        pulledTrace f g τ =
          baseChangeMate g' f' f g sq adj_f adj_f' ω ≫
            (moduleDerivedPushforward f').map e.hom ≫ twistedInverseTrace f' a' adj

/-- One-square affine base change is invertibility of the cartesian mate together
with an isomorphism of complexes commuting with `Lg^* τ` and `Tr`. -/
theorem affineBaseChangeOn_iff {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    [IsAffine Y'] [QuasiCompact f'] [QuasiSeparated f']
    (sq : IsPullback g' f' f g) (ω : ModuleDerived X)
    (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y) :
    affineBaseChangeOn f g' f' g sq ω τ ↔
      ∀ (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
        (adj : pushforwardCohomologyIn f' ⊣ a')
        (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
        (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
        [IsIso (ModuleDerived.pullbackCompComparison f' g)]
        [IsIso (ModuleDerived.pullbackCompComparison g' f)],
        IsIso (baseChangeMate g' f' f g sq adj_f adj_f' ω) ∧
          ∃ e : (ModuleDerived.pullback g').obj ω ≅ twistedInverseComplex f' a',
            pulledTrace f g τ =
              baseChangeMate g' f' f g sq adj_f adj_f' ω ≫
                (moduleDerivedPushforward f').map e.hom ≫
                  twistedInverseTrace f' a' adj :=
  sorry

/-- Pair isomorphisms to the twisted-inverse pairs on an étale covering by affine
algebraic spaces imply the affine cartesian base-change condition. -/
theorem affineBaseChangeCondition_of_etaleCovering {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Proper f] [Flat f] [FinitePresentation f]
    (ω : ModuleDerived X)
    (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y)
    {ι : Type v} {Yi : ι → AlgebraicSpace S} {Xi : ι → AlgebraicSpace S}
    (g' : ∀ i, Xi i ⟶ X) (fi : ∀ i, Xi i ⟶ Yi i) (g : ∀ i, Yi i ⟶ Y)
    (sq : ∀ i, IsPullback (g' i) (fi i) f (g i))
    (hcover : (∀ i, Etale (g i)) ∧ (⋃ i, Set.range (Points.map (g i))) = Set.univ)
    (haffine : ∀ i, IsAffine (Yi i))
    (hpair : ∀ (i : ι) [IsAffine (Yi i)] [QuasiCompact (fi i)] [QuasiSeparated (fi i)],
      affineBaseChangeOn f (g' i) (fi i) (g i) (sq i) ω τ) :
    affineBaseChangeCondition f ω τ :=
  sorry

/-- Package a `Y`-perfect pair that matches the twisted-inverse pairs on an étale
affine covering as a relative dualizing complex. -/
noncomputable def ofEtaleCovering {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Proper f] [Flat f] [FinitePresentation f]
    (ω : ModuleDerived X)
    (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y)
    (hPerfect : IsPerfectRelativeTo f ω)
    {ι : Type v} {Yi : ι → AlgebraicSpace S} {Xi : ι → AlgebraicSpace S}
    (g' : ∀ i, Xi i ⟶ X) (fi : ∀ i, Xi i ⟶ Yi i) (g : ∀ i, Yi i ⟶ Y)
    (sq : ∀ i, IsPullback (g' i) (fi i) f (g i))
    (hcover : (∀ i, Etale (g i)) ∧ (⋃ i, Set.range (Points.map (g i))) = Set.univ)
    (haffine : ∀ i, IsAffine (Yi i))
    (hpair : ∀ (i : ι) [IsAffine (Yi i)] [QuasiCompact (fi i)] [QuasiSeparated (fi i)],
      affineBaseChangeOn f (g' i) (fi i) (g i) (sq i) ω τ) :
    RelativeDualizingComplex f :=
  of f ω τ hPerfect
    (affineBaseChangeCondition_of_etaleCovering ω τ g' fi g sq hcover haffine hpair)

/-- The complex of the covering-recognized pair is the given `ω`. -/
theorem ofEtaleCovering_complex {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Proper f] [Flat f] [FinitePresentation f]
    (ω : ModuleDerived X)
    (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y)
    (hPerfect : IsPerfectRelativeTo f ω)
    {ι : Type v} {Yi : ι → AlgebraicSpace S} {Xi : ι → AlgebraicSpace S}
    (g' : ∀ i, Xi i ⟶ X) (fi : ∀ i, Xi i ⟶ Yi i) (g : ∀ i, Yi i ⟶ Y)
    (sq : ∀ i, IsPullback (g' i) (fi i) f (g i))
    (hcover : (∀ i, Etale (g i)) ∧ (⋃ i, Set.range (Points.map (g i))) = Set.univ)
    (haffine : ∀ i, IsAffine (Yi i))
    (hpair : ∀ (i : ι) [IsAffine (Yi i)] [QuasiCompact (fi i)] [QuasiSeparated (fi i)],
      affineBaseChangeOn f (g' i) (fi i) (g i) (sq i) ω τ) :
    (ofEtaleCovering ω τ hPerfect g' fi g sq hcover haffine hpair).complex = ω :=
  sorry

/-- The trace of the covering-recognized pair is the given `τ`. -/
theorem ofEtaleCovering_trace {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Proper f] [Flat f] [FinitePresentation f]
    (ω : ModuleDerived X)
    (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y)
    (hPerfect : IsPerfectRelativeTo f ω)
    {ι : Type v} {Yi : ι → AlgebraicSpace S} {Xi : ι → AlgebraicSpace S}
    (g' : ∀ i, Xi i ⟶ X) (fi : ∀ i, Xi i ⟶ Yi i) (g : ∀ i, Yi i ⟶ Y)
    (sq : ∀ i, IsPullback (g' i) (fi i) f (g i))
    (hcover : (∀ i, Etale (g i)) ∧ (⋃ i, Set.range (Points.map (g i))) = Set.univ)
    (haffine : ∀ i, IsAffine (Yi i))
    (hpair : ∀ (i : ι) [IsAffine (Yi i)] [QuasiCompact (fi i)] [QuasiSeparated (fi i)],
      affineBaseChangeOn f (g' i) (fi i) (g i) (sq i) ω τ) :
    (ofEtaleCovering ω τ hPerfect g' fi g sq hcover haffine hpair).trace = τ :=
  sorry

/-- The covering-recognized pair is `Y`-perfect and satisfies affine cartesian base
change. -/
theorem ofEtaleCovering_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Proper f] [Flat f] [FinitePresentation f]
    (ω : ModuleDerived X)
    (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y)
    (hPerfect : IsPerfectRelativeTo f ω)
    {ι : Type v} {Yi : ι → AlgebraicSpace S} {Xi : ι → AlgebraicSpace S}
    (g' : ∀ i, Xi i ⟶ X) (fi : ∀ i, Xi i ⟶ Yi i) (g : ∀ i, Yi i ⟶ Y)
    (sq : ∀ i, IsPullback (g' i) (fi i) f (g i))
    (hcover : (∀ i, Etale (g i)) ∧ (⋃ i, Set.range (Points.map (g i))) = Set.univ)
    (haffine : ∀ i, IsAffine (Yi i))
    (hpair : ∀ (i : ι) [IsAffine (Yi i)] [QuasiCompact (fi i)] [QuasiSeparated (fi i)],
      affineBaseChangeOn f (g' i) (fi i) (g i) (sq i) ω τ) :
    IsPerfectRelativeTo f
        (ofEtaleCovering ω τ hPerfect g' fi g sq hcover haffine hpair).complex ∧
      affineBaseChangeCondition f
        (ofEtaleCovering ω τ hPerfect g' fi g sq hcover haffine hpair).complex
        (ofEtaleCovering ω τ hPerfect g' fi g sq hcover haffine hpair).trace :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex
