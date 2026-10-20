/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Object
public import ReasLib.CategoryTheory.RepresentablePresheaf

/-!
@stack 017I

# Simplicial internal hom

This module owns the assumption-minimal representation API for simplicial internal hom. Given a
simplicial set `U` and a simplicial object `V`, `internalHom U V` is the chosen representing object
of the presheaf `W ↦ (copower U W ⟶ V)`, when that presheaf is representable.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject

variable {C : Type uC} [Category.{vC} C]

section MappingObject

variable (U : SSet.{uS})
variable [HasCopowers U C]

/-- The presheaf `W ↦ (copower U W ⟶ V)` on simplicial objects, assuming the copower
`copower U W` exists for every simplicial object `W`. -/
@[stacks 017I "simplicial copower mapping presheaf"]
def internalHom.presheaf (V : SimplicialObject C) : (SimplicialObject C)ᵒᵖ ⥤ Type vC :=
  (copower.functor U).op ⋙ yoneda.obj V

end MappingObject

/-- `HasInternalHom U V` records exactly that the copower mapping presheaf associated to
`U` and `V` has a representing object. -/
@[stacks 017I "existence of a simplicial internal hom"]
abbrev HasInternalHom (U : SSet.{uS}) (V : SimplicialObject C) [HasCopowers U C] : Prop :=
  Functor.IsRepresentable (internalHom.presheaf U V)

/-- `HasInternalHoms U C` says that the internal mapping object from `U` exists for every
target simplicial object in `C`. -/
@[stacks 017I "fixed-index simplicial internal homs"]
abbrev HasInternalHoms (U : SSet.{uS}) (C : Type uC) [Category.{vC} C]
    [HasCopowers U C] : Prop :=
  ∀ V : SimplicialObject C, HasInternalHom U V

section MappingObject

variable (U : SSet.{uS})
variable [HasCopowers U C]

/-- The internal hom from `U` to `V`: the representing object of the presheaf
`W ↦ (copower U W ⟶ V)`, when that presheaf is representable. -/
@[stacks 017I]
noncomputable abbrev internalHom (V : SimplicialObject C)
    [HasInternalHom U V] :
    SimplicialObject C :=
  (internalHom.presheaf U V).reprX

/-- The canonical representation carried by `internalHom U V`. Downstream APIs should use
this owner instead of unfolding the chosen representation of `internalHom.presheaf U V`. -/
@[stacks 017I "canonical representation of a simplicial internal hom"]
noncomputable abbrev internalHom.representableBy (V : SimplicialObject C)
    [HasInternalHom U V] :
    (internalHom.presheaf U V).RepresentableBy (internalHom U V) :=
  (internalHom.presheaf U V).representableBy

/-- The canonical equivalence between maps into an internal hom and maps out of the
corresponding copower. -/
@[stacks 017I "canonical simplicial internal-hom equivalence"]
noncomputable abbrev internalHom.homEquiv (V X : SimplicialObject C)
    [HasInternalHom U V] :
    (X ⟶ internalHom U V) ≃ (copower U X ⟶ V) :=
  (internalHom.representableBy U V).homEquiv

/-- Two morphisms into a chosen simplicial internal hom are equal when they induce the same
morphism out of the corresponding copower. -/
@[ext, stacks 017I "extensionality for morphisms into a simplicial internal hom"]
theorem internalHom.hom_ext {V X : SimplicialObject C} [HasInternalHom U V]
    {f g : X ⟶ internalHom U V}
    (h : internalHom.homEquiv U V X f = internalHom.homEquiv U V X g) :
    f = g := sorry

end MappingObject

end CategoryTheory.SimplicialObject
