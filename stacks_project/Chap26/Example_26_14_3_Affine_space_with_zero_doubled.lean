module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.AffinePlane

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.DoubledOrigin

variable (k : Type u) [Field k] (n : ℕ)

/- Example 26.14.3 (Affine space with zero doubled): the reusable owner supplies the concrete
glued scheme, its affine charts and fold, the global-sections comparison, and its key topological
consequences. -/
@[stacks 01JD] #check scheme k n
@[stacks 01JD "zero-section algebra map"] #check evalAtOriginAlgHom k n
#check PuncturedAffineSpace.mem_originIdeal_iff (Fin n) k
@[stacks 01JD] #check PuncturedAffineSpace.coordinateModelIso
  (ULift.{u} (Fin n)) k
@[stacks 01JD] #check
  PuncturedAffineSpace.coordinateModelIso.preimage_puncturedOpen
    (ULift.{u} (Fin n)) k
@[stacks 01JD] #check chart_cover k n
@[stacks 01JD] #check chart_isAffineOpen k n
@[stacks 01JD] #check chartComparison k n
@[stacks 01JD] #check chartIso k n
@[stacks 01JD] #check overlapMap_opensRange k n
@[stacks 01JD] #check
  PuncturedAffineSpace.DoubleAlong.overlapMap_eq_secondChart
    (ULift.{u} (Fin n)) k
@[stacks 01JD] #check fold k n
@[stacks 01JD] #check chartMap_fold k n
#check globalSectionsComparison k n
@[stacks 01JD] #check origin_images_eq k n
@[stacks 01JD] #check puncturedOpen_two_eq_puncturedAffinePlane k
@[stacks 01JD] #check chart_inf_not_isAffineOpen k

section PositiveDimension

variable (hn : 1 ≤ n)

@[stacks 01JD] #check globalSectionsComparison.isIso k n hn
@[stacks 01JD] #check not_isAffine k n hn

end PositiveDimension

section DimensionGreaterThanOne

variable (hn' : 1 < n)

@[stacks 01JD] #check chart_inf_not_isAffineOpen_of_one_lt k n hn'
@[stacks 01JD] #check infinite_irreducibleClosedSubsets k n hn'
@[stacks 01JD] #check origin_mem_irreducibleClosed_iff k n hn'

end DimensionGreaterThanOne

end AlgebraicGeometry.DoubledOrigin
