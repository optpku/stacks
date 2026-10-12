/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Preadditive.CompactObject

@[expose] public section

/-!
# Compactness relative to an object property

This module refines compactness by restricting which ambient coproducts are tested.  The
coproduct is still computed in the original category; only its colimit object is required to
satisfy the chosen object property.
-/

open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite

universe w v u

namespace CategoryTheory

variable {D : Type u} [Category.{v} D] [Preadditive D]

/-- An object `K` is compact on `P` when its preadditive coyoneda functor preserves every
ambient coproduct whose specified colimit object satisfies `P`.

The colimit is taken in `D`, not in `P.FullSubcategory`. -/
@[stacks 09J7 "relative compactness"]
def IsCompactObjectOn (P : ObjectProperty D) (K : D) : Prop :=
  ∀ (I : Type v) (F : Discrete I ⥤ D) (c : Cocone F),
    IsColimit c → P c.pt →
      PreservesColimit F (preadditiveCoyoneda.obj (op K))

namespace IsCompactObjectOn

/-- Apply relative compactness to a specified ambient coproduct, allowing any index universe
which embeds in the category's morphism universe. -/
theorem preservesColimit {P : ObjectProperty D} {K : D}
    (hK : IsCompactObjectOn P K) {I : Type w} [UnivLE.{w, v}]
    {F : Discrete I ⥤ D} {c : Cocone F} (hc : IsColimit c) (hP : P c.pt) :
    PreservesColimit F (preadditiveCoyoneda.obj (op K)) := sorry

/-- The canonical comparison from the coproduct of represented Hom groups to represented Hom of
the ambient coproduct is an isomorphism whenever that coproduct object satisfies `P`. -/
theorem isIso_sigmaComparison {P : ObjectProperty D} {K : D}
    (hK : IsCompactObjectOn P K) {I : Type w} [UnivLE.{w, v}]
    (F : I → D) [HasCoproduct F]
    [HasCoproduct (fun i ↦ (preadditiveCoyoneda.obj (op K)).obj (F i))]
    (hP : P (∐ F)) :
    IsIso (sigmaComparison (preadditiveCoyoneda.obj (op K)) F) := sorry

/-- An ordinary compact object is compact on every object property. -/
theorem of_isCompactObject (P : ObjectProperty D) (K : D) [IsCompactObject K] :
    IsCompactObjectOn P K := sorry

/-- Relative compactness is contravariant in the property of tested coproduct objects. -/
theorem mono {P Q : ObjectProperty D} (hPQ : P ≤ Q) {K : D}
    (hK : IsCompactObjectOn Q K) :
    IsCompactObjectOn P K := sorry

/-- Relative compactness is preserved under isomorphism of the representing object. -/
theorem of_iso {P : ObjectProperty D} {K L : D}
    (hK : IsCompactObjectOn P K) (e : K ≅ L) :
    IsCompactObjectOn P L := sorry

/-- If `P` is closed under coproducts of shape `I`, relative compactness induces preservation of
coproducts after restricting the represented Hom functor to `P.FullSubcategory`. -/
theorem preservesColimitsOfShape_ι {P : ObjectProperty D} {K : D}
    (hK : IsCompactObjectOn P K) (I : Type w) [UnivLE.{w, v}]
    [P.IsClosedUnderColimitsOfShape (Discrete I)] :
    PreservesColimitsOfShape (Discrete I)
      (P.ι ⋙ preadditiveCoyoneda.obj (op K)) := sorry

end IsCompactObjectOn

/-- For a fixed tested property, relative compactness is closed under isomorphisms of objects. -/
instance isCompactObjectOn_isClosedUnderIsomorphisms (P : ObjectProperty D) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsCompactObjectOn P) := sorry

/-- Testing all ambient coproducts recovers ordinary compactness. -/
theorem isCompactObjectOn_top_iff (K : D) :
    IsCompactObjectOn (⊤ : ObjectProperty D) K ↔ IsCompactObject K := sorry

end CategoryTheory
