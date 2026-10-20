module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Family.Pseudofunctor.Basic
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Computations for the pseudofunctor of selected bilimit apexes

This file exposes the five principal fields of
`BilimitConeFamily.apexPseudofunctor` through the named family-level data owners. It is a
small downstream convenience layer; the pseudofunctor structure itself and its coherence
remain in `Pseudofunctor.Basic`.
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

/-- The object action of the selected bilimit-apex pseudofunctor is the selected apex. -/
@[simp]
theorem apexPseudofunctor_obj
    (L : BilimitConeFamily (J := J) (B := B))
    (F : Pseudofunctor J B) :
    L.apexPseudofunctor.obj F = L.apex F := sorry

/-- The `1`-morphism action of the selected bilimit-apex pseudofunctor is the universal map
between the selected cones. -/
@[simp]
theorem apexPseudofunctor_map
    (L : BilimitConeFamily (J := J) (B := B))
    {E F : Pseudofunctor J B} (α : E ⟶ F) :
    L.apexPseudofunctor.map α = L.map α := sorry

/-- The `2`-morphism action of the selected bilimit-apex pseudofunctor is the induced
universal apex cell. -/
@[simp]
theorem apexPseudofunctor_map₂
    (L : BilimitConeFamily (J := J) (B := B))
    {E F : Pseudofunctor J B} {α β : E ⟶ F} (Γ : α ⟶ β) :
    L.apexPseudofunctor.map₂ Γ = L.map₂ Γ := sorry

/-- The identity comparison of the selected bilimit-apex pseudofunctor is the canonical
family-level identity comparison. -/
@[simp]
theorem apexPseudofunctor_mapId
    (L : BilimitConeFamily (J := J) (B := B))
    (F : Pseudofunctor J B) :
    L.apexPseudofunctor.mapId F = L.mapIdIso F := sorry

/-- The composition comparison of the selected bilimit-apex pseudofunctor is the canonical
family-level composition comparison. -/
@[simp]
theorem apexPseudofunctor_mapComp
    (L : BilimitConeFamily (J := J) (B := B))
    {E F G : Pseudofunctor J B} (α : E ⟶ F) (β : F ⟶ G) :
    L.apexPseudofunctor.mapComp α β =
      L.mapCompIso α β := sorry

end BilimitConeFamily

end Bicategory

end CategoryTheory
