/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Torsor.Basic

/-!
# Carrier isomorphisms of torsors

Equivariant isomorphisms of the underlying sheaves induce isomorphisms of torsors.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Sheaf.Torsor.Iso

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : Sheaf J GrpCat.{w}} {P Q : Torsor G}

/-- The inverse of an equivariant carrier isomorphism is equivariant. -/
theorem inv_comm (e : P.carrier ≅ Q.carrier)
    (h : ∀ (U : C) (g : G.1.obj (op U)) (x : P.Sections U),
      e.hom.hom.app (op U) ((P.mulAction U).smul g x) =
        (Q.mulAction U).smul g (e.hom.hom.app (op U) x))
    (U : C) (g : G.1.obj (op U)) (x : Q.Sections U) :
    e.inv.hom.app (op U) ((Q.mulAction U).smul g x) =
      (P.mulAction U).smul g (e.inv.hom.app (op U) x) := sorry

/-- An equivariant isomorphism of carrier sheaves defines an isomorphism of torsors. -/
def ofCarrierIso (e : P.carrier ≅ Q.carrier)
    (h : ∀ (U : C) (g : G.1.obj (op U)) (x : P.Sections U),
      e.hom.hom.app (op U) ((P.mulAction U).smul g x) =
        (Q.mulAction U).smul g (e.hom.hom.app (op U) x)) : Torsor.Iso P Q :=
  @CategoryTheory.Iso.mk _ Torsor.category P Q
    { hom := e.hom, comm := h }
    { hom := e.inv, comm := inv_comm e h }
    (PseudoTorsor.Hom.ext_hom e.hom_inv_id)
    (PseudoTorsor.Hom.ext_hom e.inv_hom_id)

/-- A torsor isomorphism induces the same forward and inverse maps on carrier sheaves. -/
def toCarrierIso (e : Torsor.Iso P Q) : P.carrier ≅ Q.carrier where
  hom := (@CategoryTheory.Iso.hom _ Torsor.category P Q e).hom
  inv := (@CategoryTheory.Iso.inv _ Torsor.category P Q e).hom
  hom_inv_id := congrArg (fun f : Torsor.Hom P P ↦ f.hom)
    (@CategoryTheory.Iso.hom_inv_id _ Torsor.category P Q e)
  inv_hom_id := congrArg (fun f : Torsor.Hom Q Q ↦ f.hom)
    (@CategoryTheory.Iso.inv_hom_id _ Torsor.category P Q e)

end CategoryTheory.Sheaf.Torsor.Iso
