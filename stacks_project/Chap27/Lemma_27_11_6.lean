module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.TensorProductBaseChange

@[expose] public section

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

section

variable {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
variable [Algebra R R'] [Algebra R A]
variable (calA : Nat → Submodule R A) [GradedAlgebra calA]
variable (PcalA : AlgebraicGeometry.ProjTwistPresentation calA)
variable (PcalB : AlgebraicGeometry.ProjTwistPresentation
  (AlgebraicGeometry.tensorProductBaseChangeGrading calA :
    Nat → Submodule R' (R' ⊗[R] A)))
variable (n : Int)

/- Lemma 27.11.6: for the tensor-product base change `R' ⊗[R] A`, the natural `Proj` map
has full domain. -/
@[stacks 01N2] #check
  (AlgebraicGeometry.projMapDomain_tensorProductBaseChange_eq_top (calA := calA) :
    AlgebraicGeometry.projMapDomain
        (AlgebraicGeometry.tensorProductBaseChangePsi calA :
          calA →+*ᵍ
            (AlgebraicGeometry.tensorProductBaseChangeGrading calA :
              Nat → Submodule R' (R' ⊗[R] A))) = ⊤)

#check
  (AlgebraicGeometry.projMap_tensorProductBaseChange_isPullback
      (calA := calA) (PcalA := PcalA) (PcalB := PcalB) :
    IsPullback
      (AlgebraicGeometry.tensorProductBaseChangeProjMap calA PcalA PcalB).map
      ((AlgebraicGeometry.projMapDomain
          (AlgebraicGeometry.tensorProductBaseChangePsi calA :
            calA →+*ᵍ
              (AlgebraicGeometry.tensorProductBaseChangeGrading calA :
                Nat → Submodule R' (R' ⊗[R] A)))).ι ≫
        AlgebraicGeometry.tensorProductBaseChangeProjToSpecBase calA)
      (AlgebraicGeometry.projToSpecBase calA)
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R R'))))

#check
  (AlgebraicGeometry.instIsIso_theta_tensorProductBaseChange
      (calA := calA) (PcalA := PcalA) (PcalB := PcalB) n :
    IsIso
      ((AlgebraicGeometry.tensorProductBaseChangeProjMap calA PcalA PcalB).theta n))

end
