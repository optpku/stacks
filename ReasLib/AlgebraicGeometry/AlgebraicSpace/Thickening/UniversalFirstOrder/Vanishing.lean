module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder.Vanishing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.Existence

/-!
# Vanishing of universal first-order thickenings

Conormal vanishing is expressed by vanishing of the ideal sheaf of every
compatible universal first-order thickening, without choosing a thickening.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The conormal sheaf of a morphism vanishes when the associated ideal sheaf
of every compatible universal first-order thickening vanishes. -/
def isZeroConormal {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ {X' : AlgebraicSpace S} (i : X ⟶ X') (g : X' ⟶ Y) [IsUniversalFirstOrder i g],
    i ≫ g = f → IsZero (Hom.idealSheaf i)

/-- Conormal vanishing is equivalent to vanishing of the ideal sheaf of every
compatible universal first-order thickening. -/
theorem isZeroConormal_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    isZeroConormal f ↔
      ∀ {X' : AlgebraicSpace S} (i : X ⟶ X') (g : X' ⟶ Y)
        [IsUniversalFirstOrder i g],
        i ≫ g = f → IsZero (Hom.idealSheaf i) :=
  Iff.rfl

/-- The associated ideal sheaf of any compatible universal first-order
thickening of a morphism with vanishing conormal sheaf vanishes. -/
theorem isZeroConormal_apply {S : Scheme.{u}} {X Y X' : AlgebraicSpace S}
    {f : X ⟶ Y} {i : X ⟶ X'} {g : X' ⟶ Y} [IsUniversalFirstOrder i g]
    (hfg : i ≫ g = f) (h : isZeroConormal f) :
    IsZero (Hom.idealSheaf i) :=
  h i g hfg

/-- Under formal unramifiedness, conormal vanishing is equivalent to the
existence of a compatible universal first-order thickening with vanishing
associated ideal sheaf. -/
theorem isZeroConormal_iff_exists {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FormallyUnramified f] :
    isZeroConormal f ↔
      ∃ (X' : AlgebraicSpace S) (i : X ⟶ X') (g : X' ⟶ Y),
        i ≫ g = f ∧ IsUniversalFirstOrder i g ∧ IsZero (Hom.idealSheaf i) :=
  sorry

namespace FormallyUnramified

/-- For a formally unramified morphism, the identity is a universal first-order
thickening over the target if and only if every compatible universal
first-order thickening is an isomorphism. -/
theorem isUniversalFirstOrder_id_iff_forall_isIso {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} [FormallyUnramified f] :
    IsUniversalFirstOrder (𝟙 X) f ↔
      ∀ {X' : AlgebraicSpace S} (i : X ⟶ X') (g : X' ⟶ Y)
        [IsUniversalFirstOrder i g], i ≫ g = f → IsIso i :=
  sorry

/-- For a formally unramified morphism, the identity is a universal first-order
thickening over the target if and only if the conormal sheaf vanishes. -/
theorem isUniversalFirstOrder_id_iff_isZeroConormal {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} [FormallyUnramified f] :
    IsUniversalFirstOrder (𝟙 X) f ↔ isZeroConormal f :=
  sorry

end FormallyUnramified

end AlgebraicGeometry.AlgebraicSpace
