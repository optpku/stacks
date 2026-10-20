/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Basic

/-!
# Identity comparison for pseudocone transport

This module constructs the identity comparison for mapping arbitrary conical pseudocones along
a pseudofunctor. Its apex component is exactly the ambient pseudofunctor's `mapId`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uB vB wB uD vD wD uJ vJ wJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} {D : Type uD}
variable [Bicategory.{wB, vB} B] [Bicategory.{wD, vD} D]
variable {J : Type uJ} [Bicategory.{wJ, vJ} J]

namespace Implementation

/-- Compatibility of the forward identity comparison with the mapped cone comparisons. -/
private theorem mapPseudoCone.mapId.hom.comm {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) :
    ((mapPseudoCone K S).comparison (K.obj S.pt)).map
          (K.mapId S.pt).hom ≫
        Bicategory.PseudoCone.fac (𝟙 (mapPseudoCone K S)) =
        Bicategory.PseudoCone.fac (mapPseudoCone.map K (𝟙 S)) := sorry

/-- The forward identity comparison between mapped pseudocone morphisms. -/
private def mapPseudoCone.mapId.hom {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) :
    mapPseudoCone.map K (𝟙 S) ⟶ 𝟙 (mapPseudoCone K S) :=
  Bicategory.PseudoCone.hom₂Mk
    (K.mapId S.pt).hom (mapPseudoCone.mapId.hom.comm K S)

/-- Compatibility of the inverse identity comparison with the mapped cone comparisons. -/
private theorem mapPseudoCone.mapId.inv.comm {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) :
    ((mapPseudoCone K S).comparison (K.obj S.pt)).map
          (K.mapId S.pt).inv ≫
        Bicategory.PseudoCone.fac (mapPseudoCone.map K (𝟙 S)) =
      Bicategory.PseudoCone.fac (𝟙 (mapPseudoCone K S)) := sorry

/-- The inverse identity comparison between mapped pseudocone morphisms. -/
private def mapPseudoCone.mapId.inv {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) :
    𝟙 (mapPseudoCone K S) ⟶ mapPseudoCone.map K (𝟙 S) :=
  Bicategory.PseudoCone.hom₂Mk
    (K.mapId S.pt).inv (mapPseudoCone.mapId.inv.comm K S)

/-- The forward and inverse identity comparisons cancel on the mapped identity morphism. -/
private theorem mapPseudoCone.mapId.homInvId {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) :
    mapPseudoCone.mapId.hom K S ≫ mapPseudoCone.mapId.inv K S =
      𝟙 (mapPseudoCone.map K (𝟙 S)) := sorry

/-- The inverse and forward identity comparisons cancel on the identity mapped cone
morphism. -/
private theorem mapPseudoCone.mapId.invHomId {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) :
    mapPseudoCone.mapId.inv K S ≫ mapPseudoCone.mapId.hom K S =
      𝟙 (𝟙 (mapPseudoCone K S)) := sorry

end Implementation

/-- The identity comparison for mapping conical pseudocones along a pseudofunctor. Its apex
component is the identity comparison of the ambient pseudofunctor. -/
def mapPseudoCone.mapId {E : Pseudofunctor J B} (K : Pseudofunctor B D)
    (S : Bicategory.PseudoCone E) :
    mapPseudoCone.map K (𝟙 S) ≅ 𝟙 (mapPseudoCone K S) where
  hom := Implementation.mapPseudoCone.mapId.hom K S
  inv := Implementation.mapPseudoCone.mapId.inv K S
  hom_inv_id := Implementation.mapPseudoCone.mapId.homInvId K S
  inv_hom_id := Implementation.mapPseudoCone.mapId.invHomId K S

/-- The apex cell of the forward identity comparison is `K.mapId`. -/
@[simp]
theorem mapPseudoCone.mapId.hom.apex {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) :
    Bicategory.PseudoCone.map₂ (mapPseudoCone.mapId K S).hom =
      (K.mapId S.pt).hom := sorry

/-- The apex cell of the inverse identity comparison is the inverse of `K.mapId`. -/
@[simp]
theorem mapPseudoCone.mapId.inv.apex {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) :
    Bicategory.PseudoCone.map₂ (mapPseudoCone.mapId K S).inv =
      (K.mapId S.pt).inv := sorry

/- Data audit (mathlib 4.32): `mapPseudoCone.mapId` reports `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`. Its forward and inverse apex cells are
explicitly `(K.mapId S.pt).hom` and `(K.mapId S.pt).inv`; `sorryAx` is confined to their
comparison-compatibility and inverse-law proofs and inherited coherence. -/

end Pseudofunctor

end CategoryTheory
