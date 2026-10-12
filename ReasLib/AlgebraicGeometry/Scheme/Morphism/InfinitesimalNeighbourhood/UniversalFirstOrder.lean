/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.InfinitesimalNeighbourhood.UniversalProperty
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood

/-- The first infinitesimal neighbourhood of an immersion, bundled as a thickening over
the ambient scheme. -/
def firstOrderOver {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    Thickening.Over X :=
  MorphismProperty.Arrow.mk
    (Over.homMk (fromSource i 1) (fromSource_toAmbient i 1) :
      Over.mk i ⟶ Over.mk (toAmbient i 1))
    (inferInstance : IsThickening (fromSource i 1))

/-- The closed part of `firstOrderOver i` is the source of the immersion over its target. -/
theorem firstOrderOver_left {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    (firstOrderOver i).left = Over.mk i := sorry

/-- The ambient part of `firstOrderOver i` is the first infinitesimal neighbourhood over
the target scheme. -/
theorem firstOrderOver_right {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    (firstOrderOver i).right = Over.mk (toAmbient i 1) := sorry

/-- The defining scheme morphism of `firstOrderOver i` is the canonical map from the source
to its first infinitesimal neighbourhood. -/
theorem firstOrderOver_hom {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    (Over.forget X).map (firstOrderOver i).hom = fromSource i 1 := sorry

/-- The first infinitesimal neighbourhood of an immersion is universal among first-order
thickenings over the ambient scheme. -/
theorem firstOrderOver_isUniversal {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    Thickening.IsUniversalFirstOrder (firstOrderOver i) := sorry

end AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood
