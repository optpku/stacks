module

public import ReasLib.Algebra.Category.Ring.Sheaf
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Modules over commutative-ring-valued presheaves

This leaf supplies the compatibility-level scalar-ring views used by module
presheaves. The underlying conversion itself is owned by
`CategoryTheory.Presheaf.ringPresheafOfComm`.
-/

@[expose] public section

open CategoryTheory

universe u v w

/-- The underlying `RingCat`-valued presheaf of a commutative-ring-valued presheaf.

This is the concise module-presheaf spelling of
`CategoryTheory.Presheaf.ringPresheafOfComm`. -/
@[stacks 03CU "underlying ring presheaf"]
abbrev ringPresheaf {C : Type u} [Category.{v} C]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) : Cᵒᵖ ⥤ RingCat.{w} :=
  CategoryTheory.Presheaf.ringPresheafOfComm 𝒪

namespace PresheafOfModules

/-- The morphism of underlying ring presheaves induced by a morphism of commutative-ring
presheaves. -/
@[stacks 03CU "underlying ring-presheaf map"]
abbrev presheafStructureMap {C : Type u} [Category.{v} C]
    {𝒪 𝒪' : Cᵒᵖ ⥤ CommRingCat.{w}} (α : 𝒪 ⟶ 𝒪') :
    ringPresheaf 𝒪 ⟶ ringPresheaf 𝒪' :=
  CategoryTheory.Presheaf.ringPresheafOfCommMap α

end PresheafOfModules


