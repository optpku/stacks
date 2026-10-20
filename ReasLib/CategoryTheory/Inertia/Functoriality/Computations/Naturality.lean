/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Inertia.Functoriality.Computations.Action.Objects
public import ReasLib.CategoryTheory.Inertia.Functoriality.Computations.Action.TwoCell
public import ReasLib.CategoryTheory.Inertia.Functoriality.NatTrans.Whiskering

/-!
# Naturality computations for the ordinary inertia pseudofunctor

This leaf exposes packaged `2`-cell naturality, extensionality, and compatibility with the
forgetful functor and identity section. Local hom action readouts live in
`Computations.Action.LocalAction`.
-/

@[expose] public section

open CategoryTheory
open Bicategory
open scoped Bicategory

universe u v w

namespace CategoryTheory
namespace Inertia

/-- The inertia pseudofunctor `2`-cell action is natural in inertia morphisms. -/
@[reassoc, stacks 04Z4 "inertia pseudofunctor two-cell naturality"]
theorem pseudofunctor.map₂.naturality
    {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G)
    {X Y : Inertia C} (f : X ⟶ Y) :
    ((pseudofunctor).map F).toFunctor.map f ≫
        ((pseudofunctor).map₂ η).toNatTrans.app Y =
      ((pseudofunctor).map₂ η).toNatTrans.app X ≫
        ((pseudofunctor).map G).toFunctor.map f := sorry

/-- Two inertia `2`-cell images agree when all of their inertia components agree. -/
@[stacks 04Z4 "inertia pseudofunctor two-cell extensionality"]
theorem pseudofunctor.map₂.ext
    {C D : Cat.{v, u}} {F G : C ⟶ D} {η θ : F ⟶ G}
    (h : ∀ X : Inertia C,
      ((pseudofunctor).map₂ η).toNatTrans.app X =
        ((pseudofunctor).map₂ θ).toNatTrans.app X) :
    (pseudofunctor).map₂ η = (pseudofunctor).map₂ θ := sorry

namespace pseudofunctor

namespace forget

/-- The ordinary inertia pseudofunctor commutes with forgetting the selected automorphism. -/
@[simp, stacks 042H "inertia pseudofunctor forgetful naturality"]
theorem naturality
    {C D : Cat.{v, max w v}} (F : C ⟶ D) :
    (pseudofunctor).map F ≫ (Inertia.forget D).toCatHom =
      (Inertia.forget C).toCatHom ≫ F := sorry

/-- Forgetting the selected automorphism is `2`-natural for the ordinary inertia pseudofunctor. -/
@[stacks 042H "inertia pseudofunctor forgetful two-cell naturality"]
theorem naturality₂
    {C D : Cat.{v, max w v}} {F G : C ⟶ D} (η : F ⟶ G) :
    ((pseudofunctor).map₂ η) ▷ (Inertia.forget D).toCatHom =
      eqToHom (Inertia.pseudofunctor.forget.naturality F) ≫
        (Inertia.forget C).toCatHom ◁ η ≫
        eqToHom (Inertia.pseudofunctor.forget.naturality G).symm := sorry

end forget

namespace identitySection

/-- The identity pseudofunctor map followed by the neutral section agrees with first taking the
neutral section and then applying ordinary inertia. -/
@[simp, stacks 04Z3 "inertia pseudofunctor identity-section naturality"]
theorem naturality
    {C D : Cat.{v, max w v}} (F : C ⟶ D) :
    F ≫ (Inertia.identitySection D).toCatHom =
      (Inertia.identitySection C).toCatHom ≫ (pseudofunctor).map F := sorry

/-- The identity-automorphism section is `2`-natural for the ordinary inertia pseudofunctor. -/
@[stacks 04Z3 "inertia pseudofunctor identity-section two-cell naturality"]
theorem naturality₂
    {C D : Cat.{v, max w v}} {F G : C ⟶ D} (η : F ⟶ G) :
    (Inertia.identitySection C).toCatHom ◁ ((pseudofunctor).map₂ η) =
      eqToHom (Inertia.pseudofunctor.identitySection.naturality F).symm ≫
        η ▷ (Inertia.identitySection D).toCatHom ≫
        eqToHom (Inertia.pseudofunctor.identitySection.naturality G) := sorry

end identitySection

end pseudofunctor

end Inertia
end CategoryTheory
