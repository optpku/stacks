/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Brown
import StacksCheckRecall

@[expose] public section

/- Proposition 21.43.9 (0GZ0) (1): canonical quasi-coherence on a chaotic ringed site is
strictly full, saturated, triangulated, and closed under coproducts. -/
@[stacks 0GZ0 "(1), strict fullness"]
#check @CategoryTheory.ModulesOnCategory.qc_isClosedUnderIsomorphisms

@[stacks 0GZ0 "(1), saturation"]
#check @CategoryTheory.ModulesOnCategory.qc_isStableUnderRetracts

@[stacks 0GZ0 "(1), triangulated"]
#check @CategoryTheory.ModulesOnCategory.Chaotic.isTriangulated

@[stacks 0GZ0 "(1), arbitrary coproducts"]
#check @CategoryTheory.ModulesOnCategory.Chaotic.isClosedUnderCoproducts

/- Proposition 21.43.9 (0GZ0) (2): product-preserving contravariant homological functors on
the canonical quasi-coherent derived category are representable. -/
@[stacks 0GZ0 "(2)"]
#check @CategoryTheory.ModulesOnCategory.Chaotic.existsRepresentation

/- Proposition 21.43.9 (0GZ0) (3): exact coproduct-preserving functors out of the canonical
quasi-coherent derived category have exact right adjoints. -/
@[stacks 0GZ0 "(3)"]
#check @CategoryTheory.ModulesOnCategory.Chaotic.hasExactRightAdjoint

/- Proposition 21.43.9 (0GZ0) (4): the canonical inclusion has a chosen right adjoint, and
that right adjoint is exact for the shift comparison induced by its adjunction. -/
@[stacks 0GZ0 "(4), right-adjoint existence"]
#check @CategoryTheory.ModulesOnCategory.Chaotic.inclusionIsLeftAdjoint

@[stacks 0GZ0 "(4), exact right adjoint"]
#check @CategoryTheory.ModulesOnCategory.Chaotic.inclusionRightAdjoint_isTriangulated

/- The implementation is routed through a Brown set that is small in the same universe as the
available coproducts; the ambient large object universe is not exposed as a false coproduct
requirement. -/
#check @CategoryTheory.ModulesOnCategory.Chaotic.exists_smallBrownSet
#check @CategoryTheory.BrownRepresentability.SmallSet.existsRepresentation
#check @CategoryTheory.Functor.Brown.SmallSet.hasTriangulatedRightAdjoint
#check @CategoryTheory.ModulesOnCategory.Chaotic.inclusion
