/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.SectionMap.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.RelativeProj
open Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : X ⟶ Y)
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y)}
variable (deg : DegreePieces 𝒜) {F : ProjFunctor Y 𝒜}
variable (hF : F.IsAssociatedToQuadruples deg) (L : X.Modules)
variable [isInvertibleObject L] (ψ : GradedMapToPowers f deg L)

/- Lemma 71.13.1
A graded map into powers of an invertible module determines its positive-degree
surjectivity open, a canonical morphism over the base, and a uniquely characterized
graded twist comparison. Classification of arbitrary scheme tests and compatibility
with scheme base change are checked below.
-/
@[stacks 0D2Z] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativeProj.existsUnique_twistComparison f deg hF L ψ :
    ∃! theta : TwistComparison hF (domain f deg L ψ) (canonicalMap f deg hF L ψ) L,
      ThetaCompatible f deg hF L ψ theta)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.canonicalMap_over_base f deg hF L ψ :
  canonicalMap f deg hF L ψ ≫ toAlgebraicSpace_hom F hF = (domain f deg L ψ).ι ≫ f)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.factorsThroughLift_comp f deg L ψ :
  ∀ {W : Over S} (w : ofOver W ⟶ X) (hw : memDomain f deg L ψ w),
    factorsThroughLift f deg L ψ w hw ≫ (domain f deg L ψ).ι = w)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.memDomain_of_epi f deg L ψ :
  ∀ {W : Over S} (w : ofOver W ⟶ X) (d : ℕ) (hd : 1 ≤ d)
    (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)), memDomain f deg L ψ w)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.classifiedMap_comp_of f deg hF L ψ :
  ∀ {W : Over S} (w : ofOver W ⟶ X) (d : ℕ) (hd : 1 ≤ d)
    (hEpi : Epi (restrictedDegreeMap f deg L ψ w d)),
    factorsThroughLift f deg L ψ w (memDomain_of_epi f deg L ψ w d hd hEpi) ≫
      canonicalMap f deg hF L ψ = classifiedMapOfDegree f deg hF L ψ w d hd hEpi)

section SchemeBaseChange

variable {Y' X' : Over S}
variable {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift (ofOver Y'))}
variable {deg' : DegreePieces 𝒜'} {F' : ProjFunctor (ofOver Y') 𝒜'}
variable (g : ofOver Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
variable (hF' : F'.IsAssociatedToQuadruples deg')
variable (g' : ofOver X' ⟶ X) (f' : ofOver X' ⟶ ofOver Y')
variable (hf : g' ≫ f = f' ≫ g)
variable [isInvertibleObject ((Modules.pullback g').obj L)]

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.domainBaseChangeIso_ι
  f deg L ψ g hAlg hF' g' f' hf :
  (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom ≫
    (domainInverseImage f deg L ψ g').ι =
    (domain f' deg' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).ι)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.canonicalMap_eq_baseChangeMap
  f deg L ψ hF g hAlg hF' g' f' hf :
  canonicalMap f' deg' hF' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf) =
    (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom ≫
      baseChangeMap f deg L ψ hF g hAlg hF' g' f' hf)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.canonicalMap_comp_fibre
  f deg L ψ hF g hAlg hF' g' f' hf :
  canonicalMap f' deg' hF' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf) ≫
      (canonicalBaseChangeIso g hAlg hF hF').hom =
    (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom ≫
      baseChangeToFibre f deg L ψ hF g g' f' hf)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.existsUnique_twistComparison
  f' deg' hF' ((Modules.pullback g').obj L)
    (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf) :
  ∃! theta' : TwistComparison hF'
    (domain f' deg' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf))
    (canonicalMap f' deg' hF' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf))
    ((Modules.pullback g').obj L),
    ThetaCompatible f' deg' hF' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf) theta')

variable (theta : TwistComparison hF (domain f deg L ψ) (canonicalMap f deg hF L ψ) L)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.twistComparison_pullback_compatible
  f deg L ψ hF g hAlg hF' theta g' f' hf :
  ThetaCompatible f deg hF L ψ theta →
    ThetaCompatible f' deg' hF' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)
      (TwistComparison.pullbackAlongSquare f deg L ψ hF g hAlg hF' theta g' f' hf))

end SchemeBaseChange

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
