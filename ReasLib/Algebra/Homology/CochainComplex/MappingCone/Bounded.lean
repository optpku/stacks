module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

@[expose] public section

/-!
# Boundedness of mapping cones

This leaf records the lower, upper, and two-sided boundedness of mapping cones.  The identity
specializations remain available for split-monomorphic and split-epimorphic mapping-cone
factorizations.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K L : CochainComplex C ℤ}

/-- The mapping cone of a morphism between bounded-below complexes is bounded below. -/
theorem mappingCone_plus (f : K ⟶ L) (hK : CochainComplex.plus C K)
    (hL : CochainComplex.plus C L) :
    CochainComplex.plus C (mappingCone f) := sorry

/-- The mapping cone of a morphism between bounded-above complexes is bounded above. -/
theorem mappingCone_minus (f : K ⟶ L) (hK : CochainComplex.minus C K)
    (hL : CochainComplex.minus C L) :
    CochainComplex.minus C (mappingCone f) := sorry

/-- The mapping cone of a morphism between bounded complexes is bounded. -/
theorem mappingCone_bounded (f : K ⟶ L) (hK : CochainComplex.bounded C K)
    (hL : CochainComplex.bounded C L) :
    CochainComplex.bounded C (mappingCone f) := sorry

/-- The mapping cone of the identity on a bounded-below cochain complex is bounded below. -/
theorem mappingCone_id_plus (hK : CochainComplex.plus C K) :
    CochainComplex.plus C (mappingCone (𝟙 K)) := sorry

/-- The mapping cone of the identity on a bounded-above cochain complex is bounded above. -/
theorem mappingCone_id_boundedAbove (hK : CochainComplex.minus C K) :
    CochainComplex.minus C (mappingCone (𝟙 K)) := sorry

end CochainComplex
