module

public import ReasLib.AlgebraicGeometry.Scheme.StandardZariskiCover
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u v

variable (T : Scheme.{u}) [IsAffine T]

/- Definition 34.3.4: for an affine scheme `T`, a standard Zariski cover is a finite Zariski
cover whose members identify with standard affine opens of `T`. -/
@[stacks 020R] #check
  (AlgebraicGeometry.Scheme.StandardZariskiCover.{u, v} T : Type (max u (v + 1)))
#check StandardZariskiCover.index
#check StandardZariskiCover.opens
#check StandardZariskiCover.iSup_eq_top
#check StandardZariskiCover.toOpenCover
#check StandardZariskiCover.opensRange_eq_basicOpen
#check StandardZariskiCover.isAffine_obj

end AlgebraicGeometry.Scheme
