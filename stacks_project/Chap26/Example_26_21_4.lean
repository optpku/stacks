module

public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.PuncturedAffineSpace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u


section Field

variable (k : Type u) [Field k]

/- Example 26.21.4: glue two copies of countably generated affine space along the complement
of their origin. The resulting structure morphism is not quasi-separated. -/
@[stacks 01KL] #check PuncturedAffineSpace.DoubleAlong.scheme (ULift.{u} ℕ) k
@[stacks 01KL] #check PuncturedAffineSpace.coordinateModelIso (ULift.{u} ℕ) k
@[stacks 01KL] #check PuncturedAffineSpace.coordinateModelIso.preimage_puncturedOpen
  (ULift.{u} ℕ) k
#check PuncturedAffineSpace.DoubleAlong.chart (ULift.{u} ℕ) k
#check PuncturedAffineSpace.DoubleAlong.chartComparison (ULift.{u} ℕ) k
#check PuncturedAffineSpace.DoubleAlong.chartIso (ULift.{u} ℕ) k
#check PuncturedAffineSpace.DoubleAlong.fold (ULift.{u} ℕ) k
#check PuncturedAffineSpace.DoubleAlong.toBase (ULift.{u} ℕ) k
#check PuncturedAffineSpace.DoubleAlong.chart_cover (ULift.{u} ℕ) k
#check PuncturedAffineSpace.DoubleAlong.chart_isAffineOpen (ULift.{u} ℕ) k
#check PuncturedAffineSpace.puncturedOpen.coe_eq_compl_origin (ULift.{u} ℕ) k
#check PuncturedAffineSpace.DoubleAlong.overlapMap (ULift.{u} ℕ) k
#check PuncturedAffineSpace.DoubleAlong.overlapMap_opensRange (ULift.{u} ℕ) k
#check PuncturedAffineSpace.DoubleAlong.overlapMap_eq_secondChart (ULift.{u} ℕ) k
#check PuncturedAffineSpace.DoubleAlong.origin (ULift.{u} ℕ) k 0
#check PuncturedAffineSpace.DoubleAlong.origin (ULift.{u} ℕ) k 1
#check PuncturedAffineSpace.DoubleAlong.origin_ne (ULift.{u} ℕ) k

@[stacks 01KL] #check
  PuncturedAffineSpace.DoubleAlong.toBase_not_quasiSeparated (ULift.{u} ℕ) k

@[stacks 01KL] #check
  PuncturedAffineSpace.DoubleAlong.fold_not_quasiSeparated (ULift.{u} ℕ) k

@[stacks 01KL] #check
  PuncturedAffineSpace.DoubleAlong.overlap_not_quasiCompact (ULift.{u} ℕ) k

end Field

section Generalization

variable (k : Type u) [CommRing k] [Nontrivial k]

/- Over a general nontrivial base ring, the same construction doubles the zero section rather
than a single point and still gives a non-quasi-separated morphism. -/
#check PuncturedAffineSpace.puncturedOpen.coe_eq_compl_range_zeroSection (ULift.{u} ℕ) k
#check PuncturedAffineSpace.DoubleAlong.scheme (ULift.{u} ℕ) k
#check PuncturedAffineSpace.DoubleAlong.toBase_not_quasiSeparated (ULift.{u} ℕ) k
#check PuncturedAffineSpace.DoubleAlong.fold_not_quasiSeparated (ULift.{u} ℕ) k
#check PuncturedAffineSpace.DoubleAlong.overlap_not_quasiCompact (ULift.{u} ℕ) k

end Generalization
