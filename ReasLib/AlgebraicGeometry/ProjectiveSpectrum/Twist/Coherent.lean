module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Tensor

/-!
# Coherence of twists on a projective spectrum

This leaf records the generic closure of coherent modules under tensoring by
the coherent actual twists supplied by `ProjTwistPresentation`.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.ProjTwistPresentation

variable {A sigma : Type u} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
variable {calA : Nat -> sigma} [GradedRing calA]
variable [IsLocallyNoetherian (Proj calA)]
variable [MonoidalCategory (Proj calA).Modules] [MonoidalClosed (Proj calA).Modules]

/-- Tensoring a coherent module by an actual twist from a presentation is coherent. -/
theorem tensorTwist_isCoherent
    (P : ProjTwistPresentation calA) (F : (Proj calA).Modules) [F.IsCoherent] (d : Int) :
    (P.tensorTwist F d).IsCoherent := sorry

end AlgebraicGeometry.ProjTwistPresentation
