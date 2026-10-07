module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Affine
import ReasLib.AlgebraicGeometry.PuncturedSpectrum.GlobalSections

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Remark 31.16.2: for a Noetherian normal local ring of Krull dimension at least two, the
canonical map to regular functions on the punctured spectrum is bijective. -/
@[stacks 0BCS] #check
  (@AlgebraicGeometry.PuncturedSpectrum.algebraMap_puncturedOpen_bijective :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalRing A],
      2 ≤ ringKrullDim A →
        Function.Bijective
          (algebraMap A
            ((Spec.structureSheaf A).obj.obj
              (Opposite.op (AlgebraicGeometry.PuncturedSpectrum.puncturedOpen A)) : Type u)))

/- In the same dimension range, the punctured spectrum is not affine. -/
#check
  (@AlgebraicGeometry.PuncturedSpectrum.not_isAffineOpen_of_two_le_ringKrullDim :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
      2 ≤ ringKrullDim A →
        ¬ IsAffineOpen (AlgebraicGeometry.PuncturedSpectrum.puncturedOpen A))
