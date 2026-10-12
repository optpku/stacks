/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Construction
public import ReasLib.CategoryTheory.Bicategory.LocalProperties

/-!
# Local equivalences of full-subbicategory inclusions

The inclusion attached to an implication of object properties is locally an
equivalence because it changes only object-membership witnesses.  This module
contains the corresponding hom-category inverse data and instances.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u

namespace ObjectProperty

variable {D : Type u} [Bicategory.{w, v} D]

namespace FullSubbicategory

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {P : ObjectProperty D}

namespace Implementation

/-- Mapping a lifted target cell along `ιOfLE` recovers the original target cell. -/
private theorem ιOfLEMapFunctorMapPreimage {Q : ObjectProperty D} (h : P ≤ Q)
    (X Y : P.FullSubbicategory) {f g : X ⟶ Y}
    (η : ((ιOfLE h).mapFunctor X Y).obj f ⟶
      ((ιOfLE h).mapFunctor X Y).obj g) :
    ((ιOfLE h).mapFunctor X Y).map
      (Bicategory.InducedBicategory.mkHom₂ η.hom) = η := sorry
/- Proof strategy: apply `Bicategory.InducedBicategory.hom₂_ext`; the underlying cell of the
lifted morphism is definitionally `η.hom`. -/

/-- Lifting the image of a source cell along `ιOfLE` recovers that source cell. -/
private theorem ιOfLEMapFunctorPreimageMap {Q : ObjectProperty D} (h : P ≤ Q)
    (X Y : P.FullSubbicategory) {f g : X ⟶ Y} (η : f ⟶ g) :
    (Bicategory.InducedBicategory.mkHom₂
      (((ιOfLE h).mapFunctor X Y).map η).hom : f ⟶ g) = η := sorry
/- Proof strategy: apply `Bicategory.InducedBicategory.hom₂_ext`; both sides expose the
ambient cell `η.hom`. -/

/-- The inclusion associated to `P ≤ Q` is fully faithful on every hom-category. -/
private def ιOfLEMapFunctorFullyFaithful {Q : ObjectProperty D} (h : P ≤ Q)
    (X Y : P.FullSubbicategory) : ((ιOfLE h).mapFunctor X Y).FullyFaithful where
  preimage η := Bicategory.InducedBicategory.mkHom₂ η.hom
  map_preimage := ιOfLEMapFunctorMapPreimage h X Y
  preimage_map := ιOfLEMapFunctorPreimageMap h X Y

end Implementation

namespace ιOfLE

/-- The inclusion associated to `P ≤ Q` is an equivalence on every hom category. -/
instance mapFunctorIsEquivalence {Q : ObjectProperty D} (h : P ≤ Q)
    (X Y : P.FullSubbicategory) :
    ((ιOfLE h).mapFunctor X Y).IsEquivalence := sorry
/- Proof strategy: construct `Functor.IsEquivalence` directly. Fill `faithful` and `full` from
`Implementation.ιOfLEMapFunctorFullyFaithful h X Y`; fill `essSurj` by rebuilding every target
`1`-morphism from
its ambient representative with `Bicategory.InducedBicategory.mkHom`. The equivalence class owns
the three standard derived instances. -/

/-- An inclusion induced by an implication of object properties is locally an equivalence. -/
instance isLocallyEquivalence {Q : ObjectProperty D} (h : P ≤ Q) :
    (ιOfLE h).toPseudofunctor.IsLocallyEquivalence := sorry
/- Proof strategy: supply `mapFunctorIsEquivalence h X Y` at every pair of objects. -/

end ιOfLE

end FullSubbicategory

end ObjectProperty

end CategoryTheory
