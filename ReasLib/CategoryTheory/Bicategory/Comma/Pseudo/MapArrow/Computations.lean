/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.MapArrow.Construction

/-!
# Computations for mapping bicategorical arrows

This leaf exposes the object, square, `2`-cell, and comparison data of
`Pseudofunctor.mapArrow`.  Downstream developments can simplify projected
data without unfolding the private pseudofunctor assembly.
-/

@[expose] public section

universe wA vA uA wB vB uB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace Pseudofunctor

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]

/-- Mapping an arrow object applies the pseudofunctor to its left endpoint. -/
@[simp]
theorem mapArrow.obj.left (H : A ⥤ᵖ B)
    (S : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)) :
    Bicategory.ColaxComma.left ((mapArrow H).obj S) =
      H.obj (Bicategory.ColaxComma.left S) := sorry

/-- Mapping an arrow object applies the pseudofunctor to its right endpoint. -/
@[simp]
theorem mapArrow.obj.right (H : A ⥤ᵖ B)
    (S : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)) :
    Bicategory.ColaxComma.right ((mapArrow H).obj S) =
      H.obj (Bicategory.ColaxComma.right S) := sorry

/-- Mapping an arrow object applies the pseudofunctor to its structural
`1`-morphism. -/
@[simp]
theorem mapArrow.obj.hom (H : A ⥤ᵖ B)
    (S : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)) :
    ((mapArrow H).obj S).hom = H.map S.hom := sorry

/-- Mapping an invertibly commuting square applies the pseudofunctor to its
left endpoint map. -/
@[simp]
theorem mapArrow.map.left (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    (f : S ⟶ T) :
    Bicategory.PseudoComma.left ((mapArrow H).map f) =
      H.map (Bicategory.PseudoComma.left f) := sorry

/-- Mapping an invertibly commuting square applies the pseudofunctor to its
right endpoint map. -/
@[simp]
theorem mapArrow.map.right (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    (f : S ⟶ T) :
    Bicategory.PseudoComma.right ((mapArrow H).map f) =
      H.map (Bicategory.PseudoComma.right f) := sorry

/-- The mapped comparison cell is the image of the source comparison cell
surrounded by the two composition comparisons of the pseudofunctor. -/
@[simp]
theorem mapArrow.map.cell (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    (f : S ⟶ T) :
    Bicategory.PseudoComma.cell ((mapArrow H).map f) =
      (H.mapComp (Bicategory.PseudoComma.left f) T.hom).inv ≫
        H.map₂ (Bicategory.PseudoComma.cell f) ≫
          (H.mapComp S.hom (Bicategory.PseudoComma.right f)).hom := sorry

/-- The selected comparison isomorphism of a mapped square is the mapped
source comparison surrounded by the composition comparisons of the
pseudofunctor. -/
@[simp]
theorem mapArrow.map.cellIso (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    (f : S ⟶ T) :
    Bicategory.PseudoComma.cellIso ((mapArrow H).map f) =
      ((H.mapComp (Bicategory.PseudoComma.left f) T.hom).symm ≪≫
        H.map₂Iso (Bicategory.PseudoComma.cellIso f)) ≪≫
          H.mapComp S.hom (Bicategory.PseudoComma.right f) := sorry

/-- The forward mapped comparison is the explicit pasted comparison cell. -/
@[simp]
theorem mapArrow.map.cellIso.hom (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    (f : S ⟶ T) :
    (Bicategory.PseudoComma.cellIso ((mapArrow H).map f)).hom =
      (H.mapComp (Bicategory.PseudoComma.left f) T.hom).inv ≫
        H.map₂ (Bicategory.PseudoComma.cell f) ≫
          (H.mapComp S.hom (Bicategory.PseudoComma.right f)).hom := sorry

/-- The inverse mapped comparison is the reverse paste of the source inverse
comparison and the two composition comparisons of the pseudofunctor. -/
@[simp]
theorem mapArrow.map.cellIso.inv (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    (f : S ⟶ T) :
    (Bicategory.PseudoComma.cellIso ((mapArrow H).map f)).inv =
      (H.mapComp S.hom (Bicategory.PseudoComma.right f)).inv ≫
        H.map₂ (Bicategory.PseudoComma.cellIso f).inv ≫
          (H.mapComp (Bicategory.PseudoComma.left f) T.hom).hom := sorry

/-- Mapping an arrow `2`-morphism applies the pseudofunctor to its left
endpoint cell. -/
@[simp]
theorem mapArrow.map₂.left (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    {f g : S ⟶ T} (η : f ⟶ g) :
    Bicategory.PseudoComma.left₂ ((mapArrow H).map₂ η) =
      H.map₂ (Bicategory.PseudoComma.left₂ η) := sorry

/-- Mapping an arrow `2`-morphism applies the pseudofunctor to its right
endpoint cell. -/
@[simp]
theorem mapArrow.map₂.right (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    {f g : S ⟶ T} (η : f ⟶ g) :
    Bicategory.PseudoComma.right₂ ((mapArrow H).map₂ η) =
      H.map₂ (Bicategory.PseudoComma.right₂ η) := sorry

/-- The forward identity comparison of arrow mapping is the forward identity
comparison of the pseudofunctor on the left endpoint. -/
@[simp]
theorem mapArrow.mapId.hom.left (H : A ⥤ᵖ B)
    (S : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)) :
    Bicategory.PseudoComma.left₂ ((mapArrow H).mapId S).hom =
      (H.mapId (Bicategory.ColaxComma.left S)).hom := sorry

/-- The forward identity comparison of arrow mapping is the forward identity
comparison of the pseudofunctor on the right endpoint. -/
@[simp]
theorem mapArrow.mapId.hom.right (H : A ⥤ᵖ B)
    (S : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)) :
    Bicategory.PseudoComma.right₂ ((mapArrow H).mapId S).hom =
      (H.mapId (Bicategory.ColaxComma.right S)).hom := sorry

/-- The inverse identity comparison of arrow mapping is the inverse identity
comparison of the pseudofunctor on the left endpoint. -/
@[simp]
theorem mapArrow.mapId.inv.left (H : A ⥤ᵖ B)
    (S : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)) :
    Bicategory.PseudoComma.left₂ ((mapArrow H).mapId S).inv =
      (H.mapId (Bicategory.ColaxComma.left S)).inv := sorry

/-- The inverse identity comparison of arrow mapping is the inverse identity
comparison of the pseudofunctor on the right endpoint. -/
@[simp]
theorem mapArrow.mapId.inv.right (H : A ⥤ᵖ B)
    (S : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)) :
    Bicategory.PseudoComma.right₂ ((mapArrow H).mapId S).inv =
      (H.mapId (Bicategory.ColaxComma.right S)).inv := sorry

/-- The forward composition comparison of arrow mapping is the forward
composition comparison of the pseudofunctor on the left endpoint. -/
@[simp]
theorem mapArrow.mapComp.hom.left (H : A ⥤ᵖ B)
    {S T U : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    (f : S ⟶ T) (g : T ⟶ U) :
    Bicategory.PseudoComma.left₂ ((mapArrow H).mapComp f g).hom =
      (H.mapComp (Bicategory.PseudoComma.left f)
        (Bicategory.PseudoComma.left g)).hom := sorry

/-- The forward composition comparison of arrow mapping is the forward
composition comparison of the pseudofunctor on the right endpoint. -/
@[simp]
theorem mapArrow.mapComp.hom.right (H : A ⥤ᵖ B)
    {S T U : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    (f : S ⟶ T) (g : T ⟶ U) :
    Bicategory.PseudoComma.right₂ ((mapArrow H).mapComp f g).hom =
      (H.mapComp (Bicategory.PseudoComma.right f)
        (Bicategory.PseudoComma.right g)).hom := sorry

/-- The inverse composition comparison of arrow mapping is the inverse
composition comparison of the pseudofunctor on the left endpoint. -/
@[simp]
theorem mapArrow.mapComp.inv.left (H : A ⥤ᵖ B)
    {S T U : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    (f : S ⟶ T) (g : T ⟶ U) :
    Bicategory.PseudoComma.left₂ ((mapArrow H).mapComp f g).inv =
      (H.mapComp (Bicategory.PseudoComma.left f)
        (Bicategory.PseudoComma.left g)).inv := sorry

/-- The inverse composition comparison of arrow mapping is the inverse
composition comparison of the pseudofunctor on the right endpoint. -/
@[simp]
theorem mapArrow.mapComp.inv.right (H : A ⥤ᵖ B)
    {S T U : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    (f : S ⟶ T) (g : T ⟶ U) :
    Bicategory.PseudoComma.right₂ ((mapArrow H).mapComp f g).inv =
      (H.mapComp (Bicategory.PseudoComma.right f)
        (Bicategory.PseudoComma.right g)).inv := sorry

end Pseudofunctor

end CategoryTheory
