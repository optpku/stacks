module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CotangentComplex.AffineComparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape
open Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Hom.CotangentComplex
open AlgebraicGeometry.tilde.ChangeOfRings
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 92.24.2. The canonical affine comparison is an isomorphism in the derived
category and is compatible with restriction to smaller affine opens. -/
@[stacks 08T3] #check (AlgebraicGeometry.Scheme.Hom.CotangentComplex.affineComparison_isIso :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) [hV : Fact (IsAffineOpen V)]
    (e : U ≤ f ⁻¹ᵁ V),
    IsIso (DerivedCategory.Q.map (affineComparison f hU e)))

/- The canonical affine comparison commutes with restriction to smaller affine
opens in the source and target. -/
#check (AlgebraicGeometry.Scheme.Hom.CotangentComplex.affineComparison_restrict :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U U' : X.Opens} {V V' : Y.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hUU' : U' ≤ U) (hVV' : V' ≤ V)
    (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V'),
    (Pullback.mapHomologicalComplexIso
          (X.presheaf.map (homOfLE hUU').op) (up ℤ)).hom.app
          (RingHom.cotangentComplex (f.sectionsMapAlong V U e)) ≫
        ((tilde.functor (CommRingCat.of Γ(X, U'))).mapHomologicalComplex (up ℤ)).map
          (Algebra.CotangentComplex.map (f.sectionsMapAlong V U e)
            (f.sectionsMapAlong V' U' e')
            (Y.presheaf.map (homOfLE hVV').op).hom
            (X.presheaf.map (homOfLE hUU').op).hom
            (by
              have hs := f.sectionsMapAlong_restrict V U U' e hUU'
              have ht := f.restrict_sectionsMapAlong V V' U' hVV' e'
              exact congrArg CommRingCat.Hom.hom (ht.trans hs.symm))) ≫
        affineComparison f hU' e' =
      ((Modules.pullback
            (Spec.map (X.presheaf.map (homOfLE hUU').op))).mapHomologicalComplex
          (up ℤ)).map
          (affineComparison f hU e) ≫
        (Functor.mapHomologicalComplexCompIso
          (Scheme.Modules.nestedAffinePullbackIso hU hU' hUU') (up ℤ)).hom.app
          (Hom.cotangentComplex f))

