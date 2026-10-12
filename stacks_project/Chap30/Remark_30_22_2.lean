/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.ProperFlatBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Homology
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.IsomorphismClasses

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Remark 30.22.2: a consequence of Lemma 30.22.1 is that there exists a finite complex of
finite projective `A`-modules `M` such that `H^i(X_{A'}, ℱ_{A'}) ≅ H^i(M ⊗_A A')` as
`A'`-modules for every `A`-algebra `A'`, functorially in `A'`. The left-hand side is derived
homology of `affineBaseChangedModuleDerivedGlobalSections`, and the right-hand side is ordinary
homology of the underived scalar extension of `M`. This unpacks perfectness of
`affineBaseModuleDerivedGlobalSections A f ℱ` together with the derived base-change isomorphism.
Flatness of `ℱ` over `A` is essential; see Hartshorne. -/
@[stacks 07VL]
theorem exists_boundedFiniteProjective_cohomology_extendScalars
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasPair A f]
    (ℱ : X.Modules) [ℱ.IsCoherent] (hflat : flatOver ℱ f) :
    ∃ (M : CochainComplex (ModuleCat A) ℤ),
      CochainComplex.IsBoundedFiniteProjective M ∧
        ∀ (A' : Type u) [CommRing A'] [Algebra A A']
          [AffineBaseModuleDerivedAdjunction.HasLeftDerived A'
            (Scheme.AffineBaseChange.toBase A A' f)]
          [AffineBaseModuleDerivedAdjunction.HasRightDerived A'
            (Scheme.AffineBaseChange.toBase A A' f)]
          [AffineBaseModuleDerivedAdjunction.HasPair A'
            (Scheme.AffineBaseChange.toBase A A' f)]
          [AffineBaseChangeDerivedCompatibility.HasScalarExtension A A']
          [AffineBaseChangeDerivedCompatibility.HasPullback A A' f]
          [AffineBaseChangeDerivedCompatibility.SourceRoute A A' f]
          [AffineBaseChangeDerivedCompatibility.TargetRoute A A' f]
          (i : ℤ),
          IsIsomorphic
            ((DerivedCategory.homologyFunctor (ModuleCat A') i).obj
              (affineBaseChangedModuleDerivedGlobalSections A A' f ℱ))
            ((((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj M).homology i) :=
  sorry

/-- If `M` is a bounded finite-projective model of `RΓ(X, ℱ)`, then for every `A`-algebra `A'`
the derived homology of `affineBaseChangedModuleDerivedGlobalSections` is isomorphic to the
ordinary homology of the underived scalar extension of `M`. -/
theorem homology_iso_extendScalars_of_model
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasPair A f]
    (ℱ : X.Modules) [ℱ.IsCoherent] (hflat : flatOver ℱ f)
    (M : CochainComplex (ModuleCat A) ℤ)
    (hM : CochainComplex.IsBoundedFiniteProjective M)
    (e : affineBaseModuleDerivedGlobalSections A f ℱ ≅ DerivedCategory.Q.obj M)
    {A' : Type u} [CommRing A'] [Algebra A A']
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseModuleDerivedAdjunction.HasPair A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseChangeDerivedCompatibility.HasScalarExtension A A']
    [AffineBaseChangeDerivedCompatibility.HasPullback A A' f]
    [AffineBaseChangeDerivedCompatibility.SourceRoute A A' f]
    [AffineBaseChangeDerivedCompatibility.TargetRoute A A' f]
    (i : ℤ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor (ModuleCat A') i).obj
        (affineBaseChangedModuleDerivedGlobalSections A A' f ℱ))
      ((((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M).homology i) :=
  sorry

/-- Functoriality in `A'`: there are identifications of derived homology of
`affineBaseChangedModuleDerivedGlobalSections` with homology of the underived scalar
extension of `M`, after `A → A'` and after `derivedExtensionOfScalars g`, making the square
with `derivedExtensionHomologyComparison` on the geometric side and the model-side
scalar-extension homology comparison commute. -/
theorem homology_iso_extendScalars_natural
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasPair A f]
    (ℱ : X.Modules) [ℱ.IsCoherent] (hflat : flatOver ℱ f)
    (M : CochainComplex (ModuleCat A) ℤ)
    (hM : CochainComplex.IsBoundedFiniteProjective M)
    (e : affineBaseModuleDerivedGlobalSections A f ℱ ≅ DerivedCategory.Q.obj M)
    {A' A'' : Type u} [CommRing A'] [CommRing A''] [Algebra A A'] [Algebra A A'']
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseModuleDerivedAdjunction.HasPair A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseChangeDerivedCompatibility.HasScalarExtension A A']
    [AffineBaseChangeDerivedCompatibility.HasPullback A A' f]
    [AffineBaseChangeDerivedCompatibility.SourceRoute A A' f]
    [AffineBaseChangeDerivedCompatibility.TargetRoute A A' f]
    (g : A' →ₐ[A] A'') (i : ℤ) :
    let M' := ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M
    let geo := affineBaseChangedModuleDerivedGlobalSections A A' f ℱ
    ∃ (φ' : (DerivedCategory.homologyFunctor (ModuleCat A') i).obj geo ≅ M'.homology i)
      (φ'' : (DerivedCategory.homologyFunctor (ModuleCat A'') i).obj
          ((ModuleCat.derivedExtensionOfScalars g.toRingHom).obj geo) ≅
        (((ModuleCat.extendScalars g.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M').homology i),
      ModuleCat.derivedExtensionHomologyComparison g.toRingHom geo i ≫ φ''.hom =
        (ModuleCat.extendScalars g.toRingHom).map φ'.hom ≫
          ((ModuleCat.extendScalars g.toRingHom).map
              ((DerivedCategory.homologyFunctorFactors (ModuleCat A') i).inv.app M') ≫
            ModuleCat.derivedExtensionHomologyComparison g.toRingHom
              (DerivedCategory.Q.obj M') i ≫
            (DerivedCategory.homologyFunctor (ModuleCat A'') i).map
              ((ModuleCat.derivedExtensionComplexCounit g.toRingHom).app M') ≫
            (DerivedCategory.homologyFunctorFactors (ModuleCat A'') i).hom.app
              (((ModuleCat.extendScalars g.toRingHom).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj M')) :=
  sorry

/-- In nonnegative degrees, derived homology of `affineBaseChangedModuleDerivedGlobalSections`
recovers `Scheme.Hom.cohomology` of the affine-base-changed module. -/
theorem cohomology_iso_derivedHomology
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasPair A f]
    (ℱ : X.Modules) [ℱ.IsCoherent] (hflat : flatOver ℱ f)
    {A' : Type u} [CommRing A'] [Algebra A A']
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseModuleDerivedAdjunction.HasPair A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseChangeDerivedCompatibility.HasScalarExtension A A']
    [AffineBaseChangeDerivedCompatibility.HasPullback A A' f]
    [AffineBaseChangeDerivedCompatibility.SourceRoute A A' f]
    [AffineBaseChangeDerivedCompatibility.TargetRoute A A' f]
    (i : ℕ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor (ModuleCat A') i).obj
        (affineBaseChangedModuleDerivedGlobalSections A A' f ℱ))
      (Scheme.Hom.cohomology (Scheme.AffineBaseChange.toBase A A' f)
        (AffineBaseChange.baseChange A A' f ℱ) i) :=
  sorry

end AlgebraicGeometry.Scheme.Modules
