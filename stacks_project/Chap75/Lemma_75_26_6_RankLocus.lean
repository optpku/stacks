/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Annihilator
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_26_3_FiberEulerCharacteristic
public import stacks_project.Chap75.Lemma_75_26_6_Pullback
public import stacks_project.Chap75.Lemma_75_26_4_VectorBundle

/-!
# Rank loci of derived modules on algebraic spaces

The degree-`a` rank-`r` locus of a perfect derived `𝒪_X`-module of Tor-amplitude in
`[a, b]` is the locally closed subspace of finite presentation whose functor of points
classifies morphisms along which lowest cohomology is finite locally free of rank `r`
after every further base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Module sheaves on a scheme carry the homology structure induced by their abelian
structure. -/
instance schemeModulesCategoryWithHomology (X : Scheme.{u}) :
    CategoryWithHomology X.Modules :=
  CategoryTheory.categoryWithHomology_of_abelian

end AlgebraicGeometry

namespace AlgebraicGeometry.AlgebraicSpace

/-- Restriction of modules from `ofOver U` to the underlying scheme is additive. -/
instance instAdditive_restrictToScheme {S : Scheme.{u}} (U : Over S) :
    (Modules.restrictToScheme U).Additive :=
  sorry

/-- Homotopy-to-derived restriction from `ofOver U` to the underlying scheme has a total
left derived functor. -/
instance instHasLeftDerivedFunctor_toDerived_restrictToScheme {S : Scheme.{u}}
    (U : Over S) :
    (Functor.Homotopy.toDerived (Modules.restrictToScheme U)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Modules (ofOver U)) (up ℤ)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}}

/-- Derived restriction of `D(𝒪_{ofOver U})` to the Zariski derived category of the
underlying scheme. -/
def restrictToSchemeDerived (U : Over S) :
    ModuleDerived (ofOver U) ⥤ DerivedCategory U.left.Modules :=
  Functor.LeftDerived.Homotopy.functor (Modules.restrictToScheme U)

/-- Derived restriction to the underlying scheme is the total left derived functor of
`Modules.restrictToScheme`. -/
theorem restrictToSchemeDerived_eq (U : Over S) :
    restrictToSchemeDerived U =
      Functor.LeftDerived.Homotopy.functor (Modules.restrictToScheme U) :=
  sorry

/-- The Zariski derived category of a scheme agrees with the derived category of modules
on the underlying ringed space. -/
theorem derivedCategory_modules_eq_ringedSpace (X : Scheme.{u}) :
    DerivedCategory X.Modules = RingedSpace.ModuleDerived X.toRingedSpace :=
  sorry

/-- Tor-amplitude in `[a, b]` on an algebraic space is tested after étale derived pullback
to scheme charts, reducing to `RingedSpace.HasTorAmplitudeIn`. -/
def HasTorAmplitudeIn {X : AlgebraicSpace S} (E : ModuleDerived X) (a b : ℤ) : Prop :=
  ∀ (U : Over S) (φ : ofOver U ⟶ X) [AlgebraicSpace.Etale φ],
    RingedSpace.HasTorAmplitudeIn
      (Eq.mp (derivedCategory_modules_eq_ringedSpace U.left)
        ((restrictToSchemeDerived U).obj ((pullback φ).obj E))) a b

/-- Tor-amplitude in `[a, b]` unfolds to the étale-local ringed-space condition on scheme
charts. -/
theorem hasTorAmplitudeIn_iff {X : AlgebraicSpace S} (E : ModuleDerived X) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      ∀ (U : Over S) (φ : ofOver U ⟶ X) [AlgebraicSpace.Etale φ],
        RingedSpace.HasTorAmplitudeIn
          (Eq.mp (derivedCategory_modules_eq_ringedSpace U.left)
            ((restrictToSchemeDerived U).obj ((pullback φ).obj E))) a b :=
  sorry

/-- The morphism of algebraic spaces associated to an `S`-point of `X`. -/
def homOfPoints {X : AlgebraicSpace S} {T : Over S}
    (φ : X.functorOfPoints.obj (op T)) : ofOver T ⟶ X :=
  yonedaEquiv.symm φ

/-- `homOfPoints φ` is the Yoneda inverse of the given point of `X`. -/
theorem homOfPoints_eq {X : AlgebraicSpace S} {T : Over S}
    (φ : X.functorOfPoints.obj (op T)) :
    homOfPoints φ = yonedaEquiv.symm φ :=
  sorry

/-- The functor-of-points predicate classifying morphisms along which degree-`a` cohomology
is finite locally free of rank `r` after every further scheme base change. -/
def rankLocusPredicate {X : AlgebraicSpace S} (E : ModuleDerived X) (a : ℤ) (r : ℕ)
    (T : Over S) (φ : X.functorOfPoints.obj (op T)) : Prop :=
  ∀ (T' : Over S) (g : T' ⟶ T),
    SheafOfModules.IsFiniteLocallyFreeOfRank r
      (cohomologySheaf ((pullback (ofOverMap g ≫ homOfPoints φ)).obj E) a)

/-- The functor-of-points predicate unfolds to finite locally free rank after every further
scheme base change. -/
theorem rankLocusPredicate_iff {X : AlgebraicSpace S} (E : ModuleDerived X) (a : ℤ) (r : ℕ)
    (T : Over S) (φ : X.functorOfPoints.obj (op T)) :
    rankLocusPredicate E a r T φ ↔
      ∀ (T' : Over S) (g : T' ⟶ T),
        SheafOfModules.IsFiniteLocallyFreeOfRank r
          (cohomologySheaf ((pullback (ofOverMap g ≫ homOfPoints φ)).obj E) a) :=
  sorry

/-- The subfunctor of `X.functorOfPoints` whose sections satisfy `rankLocusPredicate`. -/
def rankLocusSubfunctor {X : AlgebraicSpace S} (E : ModuleDerived X) (a : ℤ) (r : ℕ) :
    Subfunctor X.functorOfPoints where
  obj T := setOf (rankLocusPredicate E a r T.unop)
  map := sorry

/-- The object of `rankLocusSubfunctor` at `T` is the set of points satisfying the
rank-locus predicate. -/
theorem rankLocusSubfunctor_obj {X : AlgebraicSpace S} (E : ModuleDerived X) (a : ℤ)
    (r : ℕ) (T : (Over S)ᵒᵖ) :
    (rankLocusSubfunctor E a r).obj T = setOf (rankLocusPredicate E a r T.unop) :=
  sorry

/-- The degree-`a` rank-`r` locus of a derived `𝒪_X`-module, as an algebraic space over `S`. -/
def rankLocus {X : AlgebraicSpace S} (E : ModuleDerived X) (a : ℤ) (r : ℕ) :
    AlgebraicSpace S :=
  ofFunctor (rankLocusSubfunctor E a r).toFunctor sorry sorry sorry

/-- The functor of points of the rank locus is the rank-locus subfunctor. -/
theorem rankLocus_def {X : AlgebraicSpace S} (E : ModuleDerived X) (a : ℤ) (r : ℕ) :
    (rankLocus E a r).functorOfPoints = (rankLocusSubfunctor E a r).toFunctor :=
  sorry

/-- The canonical morphism from a derived rank locus to its ambient algebraic space. -/
def rankLocusι {X : AlgebraicSpace S} (E : ModuleDerived X) (a : ℤ) (r : ℕ) :
    rankLocus E a r ⟶ X :=
  (rankLocusSubfunctor E a r).ι

/-- The rank-locus inclusion is the subfunctor inclusion of `rankLocusSubfunctor`. -/
theorem rankLocusι_def {X : AlgebraicSpace S} (E : ModuleDerived X) (a : ℤ) (r : ℕ) :
    rankLocusι E a r = (rankLocusSubfunctor E a r).ι :=
  sorry

/-- Pullback to a derived rank locus preserves the lower cohomological bound coming from
the lower endpoint of a Tor-amplitude interval. -/
theorem rankLocusPullback_isGE {X : AlgebraicSpace S}
    (E : ModuleDerived X) (a b : ℤ) (r : ℕ) (hTor : HasTorAmplitudeIn E a b) :
    ((pullback (rankLocusι E a r)).obj E).IsGE a :=
  sorry

/-- The canonical comparison from pullback of lower cohomology on a rank locus to lower
cohomology after pullback along the composite morphism. -/
def rankLocusComparison {X : AlgebraicSpace S} (E : ModuleDerived X) (a : ℤ) (r : ℕ)
    {Y : AlgebraicSpace S} (g : Y ⟶ rankLocus E a r)
    (hLower : ((pullback (rankLocusι E a r)).obj E).IsGE a)
    (hSingle : IsIso (singlePullbackHomologyComparison g
      (cohomologySheaf ((pullback (rankLocusι E a r)).obj E) a) a)) :
    (Modules.pullback g).obj
        (cohomologySheaf ((pullback (rankLocusι E a r)).obj E) a) ⟶
      cohomologySheaf ((pullback (g ≫ rankLocusι E a r)).obj E) a :=
  cohomologyPullbackComparison g ((pullback (rankLocusι E a r)).obj E) a hLower hSingle ≫
    (DerivedCategory.homologyFunctor (Modules Y) a).map
      ((pullbackCompComparison g (rankLocusι E a r)).app E)

/-- The rank-locus comparison consists of the lower-edge pullback comparison followed by
the canonical derived-pullback composition comparison on cohomology. -/
theorem rankLocusComparison_def {X : AlgebraicSpace S} (E : ModuleDerived X) (a : ℤ)
    (r : ℕ) {Y : AlgebraicSpace S} (g : Y ⟶ rankLocus E a r)
    (hLower : ((pullback (rankLocusι E a r)).obj E).IsGE a)
    (hSingle : IsIso (singlePullbackHomologyComparison g
      (cohomologySheaf ((pullback (rankLocusι E a r)).obj E) a) a)) :
    rankLocusComparison E a r g hLower hSingle =
      cohomologyPullbackComparison g ((pullback (rankLocusι E a r)).obj E) a hLower hSingle ≫
        (DerivedCategory.homologyFunctor (Modules Y) a).map
          ((pullbackCompComparison g (rankLocusι E a r)).app E) :=
  sorry

/-- The scalar-action map `𝒪_Y → Hom(M, M)` on the universe-lifted commutative presentation. -/
def endomorphismAction {Y : AlgebraicSpace S} (M : Y.Modules) :
    SheafOfModules.RingedSite.unitModule (smallEtaleTopology Y) (commStructureSheafLift Y) ⟶
      (ihom (Modules.liftModule M)).obj (Modules.liftModule M) :=
  SheafOfModules.RingedSite.Annihilator.action (Modules.liftModule M)

/-- `endomorphismAction M` is the annihilator scalar-action map of the universe lift of `M`. -/
theorem endomorphismAction_eq {Y : AlgebraicSpace S} (M : Y.Modules) :
    endomorphismAction M =
      SheafOfModules.RingedSite.Annihilator.action (Modules.liftModule M) :=
  sorry

/-- For a perfect derived module with bounded Tor-amplitude, its degreewise rank-locus
morphism is an immersion. -/
theorem rankLocus_isImmersion {X : AlgebraicSpace S}
    (E : ModuleDerived X) (a b : ℤ) (r : ℕ)
    (hE : IsPerfect E) (hTor : HasTorAmplitudeIn E a b) :
    IsImmersion (rankLocusι E a r) :=
  sorry

/-- The rank locus of a perfect derived module of bounded Tor-amplitude, as a locally
closed subspace. -/
def rankLocusSubspace {X : AlgebraicSpace S} (E : ModuleDerived X) (a b : ℤ) (r : ℕ)
    (hE : IsPerfect E) (hTor : HasTorAmplitudeIn E a b) :
    LocallyClosedSubspace X where
  X := rankLocus E a r
  ι := rankLocusι E a r
  isImmersion := rankLocus_isImmersion E a b r hE hTor

/-- On the degree-`a` rank-`r` locus, degree-`a` cohomology after derived pullback is
finite locally free of rank `r`. -/
theorem rankLocus_cohomology_rank {X : AlgebraicSpace S}
    (E : ModuleDerived X) (a b : ℤ) (r : ℕ)
    (hE : IsPerfect E) (hTor : HasTorAmplitudeIn E a b) :
    SheafOfModules.IsFiniteLocallyFreeOfRank r
      (cohomologySheaf ((pullback (rankLocusι E a r)).obj E) a) :=
  sorry

/-- A morphism factors through the degree-`a` rank-`r` locus exactly when degree-`a`
cohomology is finite locally free of rank `r` after every further base change. -/
theorem rankLocus_factor_iff {X Y : AlgebraicSpace S}
    (E : ModuleDerived X) (a b : ℤ) (r : ℕ)
    (hE : IsPerfect E) (hTor : HasTorAmplitudeIn E a b) (f : Y ⟶ X) :
    Nonempty (Over.mk f ⟶ Over.mk (rankLocusι E a r)) ↔
      ∀ {Y' : AlgebraicSpace S} (g : Y' ⟶ Y),
        SheafOfModules.IsFiniteLocallyFreeOfRank r
          (cohomologySheaf ((pullback (g ≫ f)).obj E) a) :=
  sorry

/-- Factorization through the rank locus in the over-category is equivalent to the existence
of a morphism `g` with `g ≫ rankLocusι = f`. -/
theorem exists_factorization_rankLocus {X Y : AlgebraicSpace S}
    (E : ModuleDerived X) (a b : ℤ) (r : ℕ)
    (hE : IsPerfect E) (hTor : HasTorAmplitudeIn E a b) (f : Y ⟶ X) :
    Nonempty (Over.mk f ⟶ Over.mk (rankLocusι E a r)) ↔
      ∃ g : Y ⟶ rankLocus E a r, g ≫ rankLocusι E a r = f :=
  sorry

/-- The degreewise rank-locus morphism of a perfect complex with bounded Tor-amplitude is
of finite presentation. -/
theorem rankLocus_finitePresentation {X : AlgebraicSpace S}
    (E : ModuleDerived X) (a b : ℤ) (r : ℕ)
    (hE : IsPerfect E) (hTor : HasTorAmplitudeIn E a b) :
    FinitePresentation (rankLocusι E a r) :=
  sorry

/-- Pulling back lower cohomology from the rank locus agrees with lower cohomology after
derived pullback along the composite morphism. -/
theorem rankLocus_comparison_isIso {X Y : AlgebraicSpace S}
    (E : ModuleDerived X) (a b : ℤ) (r : ℕ)
    (hE : IsPerfect E) (hTor : HasTorAmplitudeIn E a b)
    (g : Y ⟶ rankLocus E a r) :
    IsIso
      (rankLocusComparison E a r g (rankLocusPullback_isGE E a b r hTor)
        (singlePullbackHomologyComparison_isIso g
          (cohomologySheaf ((pullback (rankLocusι E a r)).obj E) a) a)) :=
  sorry

/-- If all degree-`a` fiber Betti numbers are at most `r`, the degree-`a` rank-`r` locus is
closed in the ambient algebraic space. -/
theorem rankLocus_isClosedImmersion {X : AlgebraicSpace S}
    (E : ModuleDerived X) (a b : ℤ) (r : ℕ)
    (hE : IsPerfect E) (hTor : HasTorAmplitudeIn E a b)
    (hβ : ∀ x : Points X, fiberBetti E a x ≤ r) :
    IsClosedImmersion (rankLocusι E a r) :=
  sorry

/-- Under a global degree-`a` fiber Betti bound, factorization through the rank locus is
equivalent to degree-`a` cohomology after pullback being finite locally free of rank `r`. -/
theorem rankLocus_factor_iff_rank {X Y : AlgebraicSpace S}
    (E : ModuleDerived X) (a b : ℤ) (r : ℕ)
    (hE : IsPerfect E) (hTor : HasTorAmplitudeIn E a b)
    (hβ : ∀ x : Points X, fiberBetti E a x ≤ r) (f : Y ⟶ X) :
    Nonempty (Over.mk f ⟶ Over.mk (rankLocusι E a r)) ↔
      SheafOfModules.IsFiniteLocallyFreeOfRank r
        (cohomologySheaf ((pullback f).obj E) a) :=
  sorry

/-- Under a global degree-`a` fiber Betti bound by one, factorization through the rank-one
locus is equivalent to monicity of the scalar-action morphism on pulled-back cohomology. -/
theorem rankOneLocus_factor_iff_action_mono {X Y : AlgebraicSpace S}
    (E : ModuleDerived X) (a b : ℤ)
    (hE : IsPerfect E) (hTor : HasTorAmplitudeIn E a b)
    (hβ : ∀ x : Points X, fiberBetti E a x ≤ 1) (f : Y ⟶ X) :
    Nonempty (Over.mk f ⟶ Over.mk (rankLocusι E a 1)) ↔
      Mono (endomorphismAction (cohomologySheaf ((pullback f).obj E) a)) :=
  sorry

/-- An immersion of algebraic spaces is a monomorphism, so factorization through the rank
locus is unique when it exists. -/
theorem rankLocusι_mono {X : AlgebraicSpace S}
    (E : ModuleDerived X) (a b : ℤ) (r : ℕ)
    (hE : IsPerfect E) (hTor : HasTorAmplitudeIn E a b) :
    Mono (rankLocusι E a r) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
