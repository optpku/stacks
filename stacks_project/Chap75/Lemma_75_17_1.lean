module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.EndomorphismTensor
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.TensorWithObject

noncomputable section

universe u

/- Lemma 75.17.1: for a scheme `S` and an algebraic space `X` over `S`, if `K` is a complex of
𝒪_X-modules whose cohomology sheaves are quasi-coherent and `(E, d)` is its endomorphism DGA,
then the derived tensor functor `- ⊗_E^L K : D(E, d) ⟶ D(𝒪_X)` of Differential Graded Algebra
Lemma 22.35.3 has image contained in `D_QCoh(𝒪_X)`. -/
@[stacks 09MA] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.tensorFunctor_mem :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (K : CochainComplex (RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X)) ℤ)
      (hK : ∀ n : ℤ,
        SheafOfModules.isQuasicoherent (commRingedSiteLift X).structureSheaf
          (K.homology n))
      (M : DifferentialGradedModule.Derived.Category.{0, u + 1} (endDGA.{u + 1, u} K)),
      RingedSite.Hom.moduleCohomologyIn.{u + 1} (commRingedSiteLift X)
        (SheafOfModules.isQuasicoherent (commRingedSiteLift X).structureSheaf)
        ((SheafOfModules.RingedSite.TensorWithObject.Derived.tensorFunctor K).obj M))
