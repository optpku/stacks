module

public import ReasLib.CategoryTheory.Sites.Torsor.Basic

/-!
# Transport of torsors along isomorphisms of group sheaves
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Sheaf.Torsor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G H : Sheaf J GrpCat.{w}}

/-- Pulling an action back through the inverse of a group-sheaf isomorphism preserves
its unit, multiplication, naturality, transitivity, and freeness laws. -/
theorem transport_laws (e : G ≅ H) (P : Torsor G) :
    (∀ (U : C) (x : P.carrier.obj.obj (op U)),
      (fun g x ↦ (P.mulAction U).smul (e.inv.hom.app (op U) g) x) 1 x = x) ∧
    (∀ (U : C) (g h : H.obj.obj (op U)) (x : P.carrier.obj.obj (op U)),
      (fun g x ↦ (P.mulAction U).smul (e.inv.hom.app (op U) g) x) (g * h) x =
        (fun g x ↦ (P.mulAction U).smul (e.inv.hom.app (op U) g) x) g ((fun g x ↦ (P.mulAction U).smul (e.inv.hom.app (op U) g) x) h x)) ∧
    (∀ {U V : C} (f : V ⟶ U) (g : H.obj.obj (op U))
      (x : P.carrier.obj.obj (op U)),
      P.carrier.obj.map f.op ((fun g x ↦ (P.mulAction U).smul (e.inv.hom.app (op U) g) x) g x) =
        (fun g x ↦ (P.mulAction V).smul (e.inv.hom.app (op V) g) x) (H.obj.map f.op g) (P.carrier.obj.map f.op x)) ∧
    (∀ U : C, @MulAction.IsPretransitive (H.obj.obj (op U))
      (P.carrier.obj.obj (op U)) (⟨fun g x ↦ (P.mulAction U).smul (e.inv.hom.app (op U) g) x⟩ :
        SMul (H.obj.obj (op U)) (P.carrier.obj.obj (op U)))) ∧
    (∀ U : C, @IsCancelSMul (H.obj.obj (op U))
      (P.carrier.obj.obj (op U)) (⟨fun g x ↦ (P.mulAction U).smul (e.inv.hom.app (op U) g) x⟩ :
        SMul (H.obj.obj (op U)) (P.carrier.obj.obj (op U)))) := sorry

/-- Transport a torsor along an isomorphism of group sheaves, leaving its carrier unchanged
and acting by the inverse image of each section of the new group sheaf. -/
def transport (e : G ≅ H) (P : Torsor G) : Torsor H where
  carrier := P.carrier
  mulAction U :=
    { smul := (fun g x ↦ (P.mulAction U).smul (e.inv.hom.app (op U) g) x)
      one_smul := (transport_laws e P).1 U
      mul_smul := (transport_laws e P).2.1 U }
  act_naturality := (transport_laws e P).2.2.1
  isPretransitive := (transport_laws e P).2.2.2.1
  isCancelSMul := (transport_laws e P).2.2.2.2
  locallyNonempty := P.locallyNonempty

end CategoryTheory.Sheaf.Torsor
