module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Family.Map
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Functoriality.Identity
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Identity comparison for a family of selected bilimit apexes

For an explicit `BilimitConeFamily`, the universal apex map induced by the identity
diagram transformation is canonically isomorphic to the identity apex map.

The family-facing comparison is oriented as `map (𝟙 F) ≅ 𝟙 (apex F)`, matching the
`mapId` field of a pseudofunctor. Its underlying universal-lift comparison has the opposite
orientation, and both directions are exposed explicitly below.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uB vB wB uJ vJ wJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory

variable {J : Type uJ} [Bicategory.{wJ, vJ} J]
variable {B : Type uB} [Bicategory.{wB, vB} B]

namespace BilimitConeFamily

/-- The identity apex map, viewed through the selected cone's represented comparison,
presents postcomposition by the identity diagram transformation. -/
noncomputable abbrev mapIdComparisonIso
    (L : BilimitConeFamily (J := J) (B := B))
    (F : Pseudofunctor J B) :
    ((L.cone F).comparison (L.apex F)).obj (𝟙 (L.apex F)) ≅
      (PseudoCone.postcomposeObj (𝟙 F) (L.cone F)).π :=
  PseudoCone.mapDiagram.id.comparisonIso (L.cone F)

/-- The forward identity presentation is the generic bilimit identity presentation followed
by the inverse right unitor. -/
@[simp]
theorem mapIdComparisonIso_hom
    (L : BilimitConeFamily (J := J) (B := B))
    (F : Pseudofunctor J B) :
    (L.mapIdComparisonIso F).hom =
      (PseudoCone.lift.id.comparisonIso (L.cone F)).hom ≫
        (ρ_ (L.cone F).π).inv := sorry

/-- The inverse identity presentation is the right unitor followed by the inverse generic
bilimit identity presentation. -/
@[simp]
theorem mapIdComparisonIso_inv
    (L : BilimitConeFamily (J := J) (B := B))
    (F : Pseudofunctor J B) :
    (L.mapIdComparisonIso F).inv =
      (ρ_ (L.cone F).π).hom ≫
        (PseudoCone.lift.id.comparisonIso (L.cone F)).inv := sorry

/-- The identity comparison for the selected bilimit-apex assignment, oriented as required
by a pseudofunctor. -/
noncomputable abbrev mapIdIso
    (L : BilimitConeFamily (J := J) (B := B))
    (F : Pseudofunctor J B) :
    L.map (𝟙 F) ≅ 𝟙 (L.apex F) :=
  (PseudoCone.mapDiagram.id.iso (L.cone F)).symm

/-- The forward cell of the family-level identity comparison is the inverse universal-lift
identity cell. -/
@[simp]
theorem mapIdIso_hom
    (L : BilimitConeFamily (J := J) (B := B))
    (F : Pseudofunctor J B) :
    (L.mapIdIso F).hom =
      (PseudoCone.mapDiagram.id.iso (L.cone F)).inv := sorry

/-- The inverse cell of the family-level identity comparison is the forward universal-lift
identity cell. -/
@[simp]
theorem mapIdIso_inv
    (L : BilimitConeFamily (J := J) (B := B))
    (F : Pseudofunctor J B) :
    (L.mapIdIso F).inv =
      (PseudoCone.mapDiagram.id.iso (L.cone F)).hom := sorry

/-- The represented comparison sends the forward family-level identity coherence to the
inverse explicit identity presentation followed by the universal comparison. -/
@[simp]
theorem comparison_map_mapIdIso_hom
    (L : BilimitConeFamily (J := J) (B := B))
    (F : Pseudofunctor J B) :
    ((L.cone F).comparison (L.apex F)).map (L.mapIdIso F).hom =
      (L.mapIdComparisonIso F ≪≫
        (L.mapComparisonIso (𝟙 F)).symm).inv := sorry

/-- The represented comparison sends the inverse family-level identity coherence to the
forward explicit identity presentation followed by the inverse universal comparison. -/
@[simp]
theorem comparison_map_mapIdIso_inv
    (L : BilimitConeFamily (J := J) (B := B))
    (F : Pseudofunctor J B) :
    ((L.cone F).comparison (L.apex F)).map (L.mapIdIso F).inv =
      (L.mapIdComparisonIso F ≪≫
        (L.mapComparisonIso (𝟙 F)).symm).hom := sorry

/- Data and axiom audit (mathlib 4.32):

Both family-level comparison isomorphisms directly reuse the corresponding
shape-independent `PseudoCone` owners. `mapIdIso` only reverses the orientation required
by the universal-lift API; it introduces no new map, `2`-cell, or choice. -/

end BilimitConeFamily

end Bicategory

end CategoryTheory
