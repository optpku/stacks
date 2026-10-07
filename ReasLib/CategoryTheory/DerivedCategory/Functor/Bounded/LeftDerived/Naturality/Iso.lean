module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Natural isomorphisms of canonical bounded-above left-derived functors

An isomorphism of additive functors induces an isomorphism of their canonical bounded-above
left-derived functors.  The forward and inverse maps are exposed through computation lemmas.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.LeftDerived.Bounded

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- An isomorphism of additive functors induces an isomorphism of their canonical
bounded-above left-derived functors. -/
@[stacks 05T2 "natural isomorphisms of bounded-above total left-derived functors"]
noncomputable def mapIso
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (e : F ≅ G) : functor F ≅ functor G :=
  LeftDerived.mapNatIso (DerivedCategory.Minus.Qh A)
    (HomotopyCategory.Minus.quasiIso A) (NatIso.toBoundedAboveDerived e)

/-- The forward map of the induced left-derived isomorphism is induced by the forward natural
transformation. -/
@[simp]
theorem mapIso_hom
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (e : F ≅ G) :
    (mapIso e).hom = map e.hom := sorry

/-- The inverse map of the induced left-derived isomorphism is induced by the inverse natural
transformation. -/
@[simp]
theorem mapIso_inv
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (e : F ≅ G) :
    (mapIso e).inv = map e.inv := sorry

/-- The bounded-above left-derived action preserves reflexive natural isomorphisms. -/
@[simp, stacks 05T2 "bounded-above left-derived natural isomorphism identity"]
theorem mapIso_refl
    (F : A ⥤ B) [F.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)] :
    mapIso (Iso.refl F) = Iso.refl (functor F) := sorry

/-- The bounded-above left-derived action preserves symmetry of natural isomorphisms. -/
@[simp, stacks 05T2 "bounded-above left-derived natural isomorphism symmetry"]
theorem mapIso_symm
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (e : F ≅ G) :
    mapIso e.symm = (mapIso e).symm := sorry

/-- The bounded-above left-derived action preserves transitivity of natural isomorphisms. -/
@[simp, stacks 05T2 "bounded-above left-derived natural isomorphism composition"]
theorem mapIso_trans
    {F G H : A ⥤ B} [F.Additive] [G.Additive] [H.Additive]
    [F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [G.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    [H.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (e : F ≅ G) (e' : G ≅ H) :
    mapIso (e ≪≫ e') = mapIso e ≪≫ mapIso e' := sorry

end CategoryTheory.Functor.LeftDerived.Bounded
