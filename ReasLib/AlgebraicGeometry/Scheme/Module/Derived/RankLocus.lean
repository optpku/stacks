module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Annihilator
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FiberBetti
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Locus.Flat

@[expose] public section

/-!
# Rank loci of derived modules

This module constructs the degreewise rank locus of a derived module and records its
geometric and base-change properties at the lower endpoint of a Tor-amplitude interval.
-/

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived.Cohomology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X : Scheme.{u}}

/-- The rank-`r` locus of degree-`a` cohomology is the corresponding Fitting rank locus. -/
def rankLocus (E : RingedSpace.ModuleDerived X.toRingedSpace) (a : ℤ) (r : ℕ) :
    Scheme.{u} :=
  Scheme.fittingRankLocus (RingedSpace.ModuleDerived.cohomologySheaf E a) r

/-- The derived rank locus agrees with the Fitting rank locus of the corresponding
cohomology sheaf. -/
theorem rankLocus_def (E : RingedSpace.ModuleDerived X.toRingedSpace) (a : ℤ) (r : ℕ) :
    rankLocus E a r =
      Scheme.fittingRankLocus (RingedSpace.ModuleDerived.cohomologySheaf E a) r := sorry

/-- The canonical morphism from a derived rank locus to its ambient scheme. -/
def rankLocusι (E : RingedSpace.ModuleDerived X.toRingedSpace) (a : ℤ) (r : ℕ) :
    rankLocus E a r ⟶ X :=
  Scheme.fittingRankLocusι (RingedSpace.ModuleDerived.cohomologySheaf E a) r

/-- The morphism from a derived rank locus agrees with the canonical Fitting-locus
morphism. -/
theorem rankLocusι_def (E : RingedSpace.ModuleDerived X.toRingedSpace) (a : ℤ) (r : ℕ) :
    rankLocusι E a r =
      Scheme.fittingRankLocusι (RingedSpace.ModuleDerived.cohomologySheaf E a) r := sorry

/-- The canonical morphism from a derived rank locus is an immersion. -/
instance rankLocusι_isImmersion
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (a : ℤ) (r : ℕ) :
    IsImmersion (rankLocusι E a r) := sorry

/-- Pullback to a derived rank locus preserves the lower cohomological bound coming from
the lower endpoint of a Tor-amplitude interval. -/
theorem rankLocusPullback_isGE
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (a b : ℤ) (r : ℕ)
    (hTor : RingedSpace.HasTorAmplitudeIn E a b) :
    ((RingedSpace.modulePullbackDerived (rankLocusι E a r).toShHom).obj E).IsGE a := sorry

/-- The canonical comparison from pullback of lower cohomology on a rank locus to lower
cohomology after pullback along the composite morphism. -/
noncomputable def rankLocusComparison
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (a : ℤ) (r : ℕ)
    {Y : Scheme.{u}} (g : Y ⟶ rankLocus E a r)
    (hLower :
      ((RingedSpace.modulePullbackDerived (rankLocusι E a r).toShHom).obj E).IsGE a)
    (hSingle : IsIso
      (singlePullbackHomologyComparison g.toShHom
        (RingedSpace.ModuleDerived.cohomologySheaf
          ((RingedSpace.modulePullbackDerived (rankLocusι E a r).toShHom).obj E) a) a)) :
    (RingedSpace.Hom.pullback g.toShHom).obj
        (RingedSpace.ModuleDerived.cohomologySheaf
          ((RingedSpace.modulePullbackDerived (rankLocusι E a r).toShHom).obj E) a) ⟶
      RingedSpace.ModuleDerived.cohomologySheaf
        ((RingedSpace.modulePullbackDerived
          (g.toShHom ≫ (rankLocusι E a r).toShHom)).obj E) a :=
  lowerPullbackComparison g.toShHom
      ((RingedSpace.modulePullbackDerived (rankLocusι E a r).toShHom).obj E) a
      hLower hSingle ≫
    (DerivedCategory.homologyFunctor Y.toRingedSpace.Modules a).map
      ((RingedSpace.modulePullbackDerived.compComparison
        g.toShHom (rankLocusι E a r).toShHom).app E)

/-- The rank-locus comparison consists of the lower-edge pullback comparison followed by
the canonical derived-pullback composition comparison on cohomology. -/
theorem rankLocusComparison_def
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (a : ℤ) (r : ℕ)
    {Y : Scheme.{u}} (g : Y ⟶ rankLocus E a r)
    (hLower :
      ((RingedSpace.modulePullbackDerived (rankLocusι E a r).toShHom).obj E).IsGE a)
    (hSingle : IsIso
      (singlePullbackHomologyComparison g.toShHom
        (RingedSpace.ModuleDerived.cohomologySheaf
          ((RingedSpace.modulePullbackDerived (rankLocusι E a r).toShHom).obj E) a) a)) :
    rankLocusComparison E a r g hLower hSingle =
      lowerPullbackComparison g.toShHom
          ((RingedSpace.modulePullbackDerived (rankLocusι E a r).toShHom).obj E) a
          hLower hSingle ≫
        (DerivedCategory.homologyFunctor Y.toRingedSpace.Modules a).map
          ((RingedSpace.modulePullbackDerived.compComparison
            g.toShHom (rankLocusι E a r).toShHom).app E) := sorry

/-- For a perfect derived module with bounded Tor-amplitude, its degreewise rank-locus
morphism is an immersion. -/
theorem rankLocus_isImmersion {X : Scheme.{u}}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (a b : ℤ) (r : ℕ)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (hTor : RingedSpace.HasTorAmplitudeIn E a b) :
    IsImmersion (rankLocusι E a r) := sorry

/-- On the degree-`a` rank-`r` locus, degree-`a` cohomology after derived pullback is
finite locally free of rank `r`. -/
theorem rankLocus_cohomology_rank {X : Scheme.{u}}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (a b : ℤ) (r : ℕ)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (hTor : RingedSpace.HasTorAmplitudeIn E a b) :
    SheafOfModules.IsFiniteLocallyFreeOfRank r
      (RingedSpace.ModuleDerived.cohomologySheaf
        ((RingedSpace.modulePullbackDerived (rankLocusι E a r).toShHom).obj E) a) := sorry

/-- A morphism factors through the degree-`a` rank-`r` locus exactly when degree-`a`
cohomology is finite locally free of rank `r` after every further base change. -/
theorem rankLocus_factor_iff {X Y : Scheme.{u}}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (a b : ℤ) (r : ℕ)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (hTor : RingedSpace.HasTorAmplitudeIn E a b) (f : Y ⟶ X) :
    Nonempty (Over.mk f ⟶ Over.mk (rankLocusι E a r)) ↔
      ∀ {Y' : Scheme.{u}} (g : Y' ⟶ Y),
        SheafOfModules.IsFiniteLocallyFreeOfRank r
          (RingedSpace.ModuleDerived.cohomologySheaf
            ((RingedSpace.modulePullbackDerived (g ≫ f).toShHom).obj E) a) := sorry

/-- The degreewise rank-locus morphism of a perfect complex with bounded Tor-amplitude is
of finite presentation. -/
theorem rankLocus_finitePresentation {X : Scheme.{u}}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (a b : ℤ) (r : ℕ)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (hTor : RingedSpace.HasTorAmplitudeIn E a b) :
    Scheme.Hom.FinitePresentation (rankLocusι E a r) := sorry

/-- Pulling back lower cohomology from the rank locus agrees with lower cohomology after
derived pullback along the composite morphism. -/
theorem rankLocus_comparison_isIso {X Y : Scheme.{u}}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (a b : ℤ) (r : ℕ)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (hTor : RingedSpace.HasTorAmplitudeIn E a b) (g : Y ⟶ rankLocus E a r) :
    IsIso
      (rankLocusComparison E a r g (rankLocusPullback_isGE E a b r hTor)
        (singlePullbackHomologyComparison_isIso
          g.toShHom
          (RingedSpace.ModuleDerived.cohomologySheaf
            ((RingedSpace.modulePullbackDerived (rankLocusι E a r).toShHom).obj E) a) a)) := sorry

/-- If all degree-`a` fiber Betti numbers are at most `r`, the degree-`a` rank-`r` locus is
closed in the ambient scheme. -/
theorem rankLocus_isClosedImmersion {X : Scheme.{u}}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (a b : ℤ) (r : ℕ)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (hTor : RingedSpace.HasTorAmplitudeIn E a b)
    (hβ : ∀ x : X, fiberBetti E a x ≤ r) :
    IsClosedImmersion (rankLocusι E a r) := sorry

/-- Under a global degree-`a` fiber Betti bound, factorization through the rank locus is
equivalent to degree-`a` cohomology after pullback being finite locally free of rank `r`. -/
theorem rankLocus_factor_iff_rank {X Y : Scheme.{u}}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (a b : ℤ) (r : ℕ)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (hTor : RingedSpace.HasTorAmplitudeIn E a b)
    (hβ : ∀ x : X, fiberBetti E a x ≤ r) (f : Y ⟶ X) :
    Nonempty (Over.mk f ⟶ Over.mk (rankLocusι E a r)) ↔
      SheafOfModules.IsFiniteLocallyFreeOfRank r
        (RingedSpace.ModuleDerived.cohomologySheaf
          ((RingedSpace.modulePullbackDerived f.toShHom).obj E) a) := sorry

/-- Under a global degree-`a` fiber Betti bound by one, factorization through the rank-one
locus is equivalent to monicity of the scalar-action morphism on pulled-back cohomology. -/
theorem rankOneLocus_factor_iff_action_mono {X Y : Scheme.{u}}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (a b : ℤ)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (hTor : RingedSpace.HasTorAmplitudeIn E a b)
    (hβ : ∀ x : X, fiberBetti E a x ≤ 1) (f : Y ⟶ X) :
    Nonempty (Over.mk f ⟶ Over.mk (rankLocusι E a 1)) ↔
      Mono (SheafOfModules.Annihilator.action
        (RingedSpace.ModuleDerived.cohomologySheaf
          ((RingedSpace.modulePullbackDerived f.toShHom).obj E) a)) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
