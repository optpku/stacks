module

public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.Limit
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Successor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Matching maps of simplicial objects

This leaf owns the canonical comparison from a simplicial object to the coskeleton of its
truncation. Site-theoretic hypercovering conditions specialize this neutral construction.
-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject

open Opposite
open CategoryTheory.Limits
open scoped Simplicial

variable {C : Type u} [Category.{v} C]

/-- The canonical degree-`n + 1` comparison from a simplicial object to the coskeleton of its
`n`-truncation. -/
@[stacks 01G5 "simplicial matching map"]
noncomputable abbrev matchingMap (K : SimplicialObject C) (n : ℕ)
    [Truncated.HasCoskeletons C n] :
    K.obj (op <| SimplexCategory.mk (n + 1)) ⟶
      ((cosk n).obj K).obj (op <| SimplexCategory.mk (n + 1)) :=
  ((coskAdj n).unit.app K).app (op <| SimplexCategory.mk (n + 1))

/-- Unfolding the matching map gives the corresponding coskeleton-unit component. -/
@[simp] theorem matchingMap_def (K : SimplicialObject C) (n : ℕ)
    [Truncated.HasCoskeletons C n] :
    matchingMap K n =
      ((coskAdj n).unit.app K).app (op <| SimplexCategory.mk (n + 1)) := sorry

namespace matchingMap

/-- The compatible family of top faces of a simplicial object, viewed in the matching presheaf of
its `n`-truncation. -/
@[stacks 0189 "face family of a simplicial matching map"]
def faceFamily (K : SimplicialObject C) (n : ℕ) :
    SimplicialObject.Truncated.matching.FaceFamily ((truncation n).obj K)
      (K.obj (op <| SimplexCategory.mk (n + 1))) where
  app i := K.δ i
  compatible := sorry

/-- The matching map with its target identified as the canonical limit matching object. -/
@[stacks 0189 "matching map into the canonical matching object"]
noncomputable def toObject (K : SimplicialObject C) (n : ℕ)
    [HasLimit (SimplicialObject.Truncated.matching.diagram ((truncation n).obj K))] :
    K.obj (op <| SimplexCategory.mk (n + 1)) ⟶
      SimplicialObject.Truncated.matching.object ((truncation n).obj K) :=
  (SimplicialObject.Truncated.matching.object.representableBy
      ((truncation n).obj K)).homEquiv.symm (faceFamily K n)

/-- The canonical matching-object map has the prescribed top-face coordinates. -/
@[reassoc (attr := simp), stacks 0189 "matching map face coordinates"]
theorem toObject_face (K : SimplicialObject C) (n : ℕ)
    [HasLimit (SimplicialObject.Truncated.matching.diagram ((truncation n).obj K))]
    (i : Fin (n + 2)) :
    toObject K n ≫
        SimplicialObject.Truncated.matching.object.face ((truncation n).obj K) i =
      K.δ i := sorry

/-- Matching maps are natural in the simplicial object. -/
@[reassoc (attr := simp), stacks 0189 "naturality of matching maps"]
theorem toObject_naturality {K L : SimplicialObject C} (n : ℕ)
    [HasLimit (SimplicialObject.Truncated.matching.diagram ((truncation n).obj K))]
    [HasLimit (SimplicialObject.Truncated.matching.diagram ((truncation n).obj L))]
    (f : K ⟶ L) :
    f.app (op <| SimplexCategory.mk (n + 1)) ≫ toObject L n =
      toObject K n ≫
        SimplicialObject.Truncated.matching.map ((truncation n).map f) := sorry

/-- The canonical matching maps assemble into a natural transformation from evaluation in the
first omitted degree to the matching object of the truncation. Unlike `matchingMap`, this bundled
form needs only the matching limits at the fixed truncation level. -/
@[stacks 0189 "natural transformation of matching maps"]
noncomputable def natTrans (n : ℕ)
    [SimplicialObject.Truncated.HasMatchingObjects C n] :
    (evaluation SimplexCategoryᵒᵖ C).obj
        (op <| SimplexCategory.mk (n + 1)) ⟶
      truncation n ⋙ SimplicialObject.Truncated.matching.functor (C := C) n where
  app K := toObject K n
  naturality := fun {_ _} f ↦ toObject_naturality n f

/-- A component of the natural matching map is the canonical map to the matching limit. -/
@[simp, stacks 0189 "component of the natural matching map"]
theorem natTrans_app (n : ℕ) [SimplicialObject.Truncated.HasMatchingObjects C n]
    (K : SimplicialObject C) :
    (natTrans (C := C) n).app K = toObject K n := sorry

/-- The chosen pointwise coskeleton in degree `n + 1` is canonically the matching object. This
objectwise comparison only assumes a pointwise coskeleton for the particular truncation of `K`. -/
@[stacks 0189 "coskeleton matching map comparison"]
noncomputable def objectIso (K : SimplicialObject C) (n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseCoskeleton ((truncation n).obj K)] :
    ((truncation n).obj K).coskeleton.obj (op <| SimplexCategory.mk (n + 1)) ≅
      SimplicialObject.Truncated.matching.object ((truncation n).obj K) :=
  ((SimplicialObject.Truncated.Between.coskeleton.restriction.iso
      ((truncation n).obj K) (n + 1) (Nat.le_succ n)).app
      (SimplicialObject.Truncated.successor.top n)).symm ≪≫
    SimplicialObject.Truncated.trunc.cosk.succ.top.iso n ((truncation n).obj K)

/-- Composing the global coskeleton-unit matching map with the objectwise comparison gives
`toObject`. The global assumption occurs only here because `matchingMap` is the component of
Mathlib's category-wide coskeleton adjunction. -/
@[reassoc (attr := simp), stacks 0189 "matching map comparison formula"]
theorem comp_objectIso_hom (K : SimplicialObject C) (n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n] :
    matchingMap K n ≫ (objectIso K n).hom =
      toObject K n := sorry

end matchingMap

end CategoryTheory.SimplicialObject
