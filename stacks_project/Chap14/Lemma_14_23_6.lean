module

public import ReasLib.AlgebraicTopology.DoldKan.DegenerateDecomposition.Comparison
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.LowerFace.Decomposition
import StacksCheckRecall

@[expose] public section

/-!
# Source-facing bridge for Lemma 14.23.6

@stack 019A

The normalized-plus-degenerate decomposition and its naturality API are owned by ReasLib.
-/

open CategoryTheory AlgebraicTopology
open scoped DoldKan

universe v u

namespace AlgebraicTopology.DoldKan

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (U : SimplicialObject A)

/- Lemma 14.23.6 (1): the source-signed normalized Moore inclusion is canonically split. -/
@[stacks 019A "Lemma 14.23.6 (1)"]
#check (AlgebraicTopology.normalizedMooreComplex.lowerFace.inclusion.appSplitMono U :
  SplitMono (AlgebraicTopology.normalizedMooreComplex.lowerFace.inclusion.app U))
#check (inferInstance : IsSplitMono
  (AlgebraicTopology.normalizedMooreComplex.lowerFace.inclusion.app U))

#check (AlgebraicTopology.normalizedMooreComplex.lowerFace.inclusion.splitMono (A := A) :
  SplitMono (AlgebraicTopology.normalizedMooreComplex.lowerFace.inclusion.natTrans (A := A)))
#check (inferInstance : IsSplitMono
  (AlgebraicTopology.normalizedMooreComplex.lowerFace.inclusion.natTrans (A := A)))

@[stacks 019A "source-signed normalized projection split epimorphism"]
#check (AlgebraicTopology.normalizedMooreComplex.lowerFace.projection.appSplitEpi U :
  SplitEpi (AlgebraicTopology.normalizedMooreComplex.lowerFace.projection U))
#check (inferInstance : IsSplitEpi
  (AlgebraicTopology.normalizedMooreComplex.lowerFace.projection U))
#check (AlgebraicTopology.normalizedMooreComplex.lowerFace.projection.splitEpi (A := A) :
  SplitEpi (AlgebraicTopology.normalizedMooreComplex.lowerFace.projection.natTrans (A := A)))

/- The source-signed owner exposes the component data and its natural form. -/
#check (AlgebraicTopology.normalizedMooreComplex.lowerFace.inclusion.natTrans (A := A) :
  AlgebraicTopology.normalizedMooreComplex.lowerFace (A := A) ⟶
    alternatingFaceMapComplex A)

/- The degenerate retract exposes the complementary source summand. -/
#check AlgebraicTopology.normalizedMooreComplex.lowerFace.degenerate.projector U
#check AlgebraicTopology.normalizedMooreComplex.lowerFace.degenerate.projection U
#check AlgebraicTopology.normalizedMooreComplex.lowerFace.degenerate.projection.appSplitEpi U
#check (inferInstance : IsSplitEpi
  (AlgebraicTopology.normalizedMooreComplex.lowerFace.degenerate.projection U))
#check (AlgebraicTopology.normalizedMooreComplex.lowerFace.degenerate.projection.splitEpi (A := A) :
  SplitEpi
    (AlgebraicTopology.normalizedMooreComplex.lowerFace.degenerate.projection.natTrans (A := A)))
#check (AlgebraicTopology.normalizedMooreComplex.lowerFace.degenerate.ι.appSplitMono U :
  SplitMono (degenerateComplex.ι U))
#check (inferInstance : IsSplitMono (degenerateComplex.ι U))

/- Lemma 14.23.6 (2): the source alternating-face complex is the biproduct of its source-signed
normalized and degenerate summands. -/
@[stacks 019A "Lemma 14.23.6 (2)"]
#check (AlgebraicTopology.normalizedMooreComplex.lowerFace.decomposition.iso U :
  K[U] ≅ (AlgebraicTopology.normalizedMooreComplex.lowerFace.obj U) ⊞ D[U])
#check AlgebraicTopology.normalizedMooreComplex.lowerFace.decomposition.bicone U
#check AlgebraicTopology.normalizedMooreComplex.lowerFace.decomposition.isBilimit U
#check AlgebraicTopology.normalizedMooreComplex.lowerFace.inclusion.cokernelIso U
#check AlgebraicTopology.normalizedMooreComplex.lowerFace.degenerate.ι.cokernelIso U
#check AlgebraicTopology.normalizedMooreComplex.lowerFace.projection.kernelIso U
#check AlgebraicTopology.normalizedMooreComplex.lowerFace.degenerate.projection.kernelIso U

/- Lemma 14.23.6 (3): the source-signed decomposition is functorial. -/
@[stacks 019A "Lemma 14.23.6 (3)"]
#check (AlgebraicTopology.normalizedMooreComplex.lowerFace.decomposition.natIso (A := A) :
  alternatingFaceMapComplex A ≅
    (AlgebraicTopology.normalizedMooreComplex.lowerFace (A := A)) ⊞
      degenerateComplex.functor (C := A))
#check AlgebraicTopology.normalizedMooreComplex.lowerFace.decomposition.natIso.app

/- The Mathlib d₀ and `QInfty` decompositions remain available as convention-specific companions. -/
#check (normalizedMooreComplex.inclusion.appSplitMono U :
  SplitMono (inclusionOfMooreComplexMap U))
#check (inferInstance : IsSplitMono (inclusionOfMooreComplexMap U))
#check (normalizedMooreComplex.inclusion.splitMono A :
  SplitMono (inclusionOfMooreComplex A))
#check (inferInstance : IsSplitEpi (PInftyToNormalizedMooreComplex U))
#check (AlgebraicTopology.DoldKan.QInfty.image U)
#check (AlgebraicTopology.DoldKan.QInfty.toImage U)
#check (AlgebraicTopology.DoldKan.QInfty.fromImage U)
#check (inferInstance : IsSplitMono
  (AlgebraicTopology.DoldKan.QInfty.fromImage.natTrans (C := A)))
#check (inferInstance : IsSplitEpi
  (AlgebraicTopology.DoldKan.QInfty.toImage.natTrans (C := A)))
variable (n : ℕ)
#check AlgebraicTopology.DoldKan.QInfty.evalImageIso U n
#check AlgebraicTopology.DoldKan.QInfty.degreeIso U n
#check AlgebraicTopology.DoldKan.QInfty.degreeProjection U n
#check AlgebraicTopology.DoldKan.QInfty.degreeSubobject_eq U n
#check AlgebraicTopology.DoldKan.QInfty.imageComparison.evalIso.eq_degreeIso U n

#check (AlgebraicTopology.DoldKan.QInfty.decomposition U :
  K[U] ≅ N[U] ⊞ AlgebraicTopology.DoldKan.QInfty.image U)

/- The degreewise `D[U]` presentation remains available as the source-facing comparison. -/
#check (degenerateComplex.decomposition U : K[U] ≅ N[U] ⊞ D[U])
#check degenerateComplex.decomposition.eq_canonical U

#check (AlgebraicTopology.DoldKan.QInfty.imageFunctor (C := A) :
  SimplicialObject A ⥤ ChainComplex A ℕ)

#check (degenerateComplex.functor (C := A) :
  SimplicialObject A ⥤ ChainComplex A ℕ)
#check (AlgebraicTopology.DoldKan.QInfty.imageComparison.natIso (C := A) :
  AlgebraicTopology.DoldKan.QInfty.imageFunctor (C := A) ≅
    degenerateComplex.functor (C := A))

/- The d₀-oriented natural decompositions are companion APIs. -/
#check (AlgebraicTopology.DoldKan.QInfty.decomposition.natIso (A := A) :
  alternatingFaceMapComplex A ≅
    (normalizedMooreComplex A) ⊞
      AlgebraicTopology.DoldKan.QInfty.imageFunctor (C := A))

#check (degenerateComplex.decomposition.natIso (A := A) :
  alternatingFaceMapComplex A ≅
    (normalizedMooreComplex A) ⊞ degenerateComplex.functor (C := A))
#check degenerateComplex.decomposition.natIso.eq_canonical (A := A)

end AlgebraicTopology.DoldKan
