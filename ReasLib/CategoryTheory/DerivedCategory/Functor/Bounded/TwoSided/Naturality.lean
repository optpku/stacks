/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.TwoSided.Basic
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Map.Naturality.Bounded

/-!
# Naturality of two-sided bounded induced functors

An additive natural transformation induces a natural transformation on bounded derived
categories. The construction is obtained by applying the bounded homotopy naturality API and
then localizing.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.NatTrans

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Preadditive A] [Abelian B] [HasDerivedCategory.{w} B]
  {F G H : A ⥤ B} [F.Additive] [G.Additive] [H.Additive]

/-- An additive natural transformation induces a natural transformation between the associated
functors `Kᵇ(A) ⟶ Dᵇ(B)`. -/
@[stacks 05T4 "bounded derived natural transformation"]
noncomputable def toBoundedDerived (f : F ⟶ G) :
    F.toBoundedDerived ⟶ G.toBoundedDerived :=
  Functor.whiskerRight (Functor.Homotopy.Bounded.natTrans f)
    (DerivedCategory.Bounded.Qh B)

/-- The component of `toBoundedDerived f` is obtained by applying the bounded localization
functor to the corresponding homotopy-category component. -/
@[simp, stacks 05T4 "bounded derived natural transformation computation"]
theorem toBoundedDerived_app (f : F ⟶ G) (K : HomotopyCategory.Bounded A) :
    (toBoundedDerived f).app K =
      (DerivedCategory.Bounded.Qh B).map
        ((Functor.Homotopy.Bounded.natTrans f).app K) := sorry

/-- The bounded derived action preserves identity natural transformations. -/
@[simp, stacks 05T4 "bounded derived natural transformation identity"]
theorem toBoundedDerived_id :
    toBoundedDerived (𝟙 F) = 𝟙 F.toBoundedDerived := sorry

/-- The bounded derived action preserves vertical composition. -/
@[simp, stacks 05T4 "bounded derived natural transformation composition"]
theorem toBoundedDerived_comp (f : F ⟶ G) (g : G ⟶ H) :
    toBoundedDerived (f ≫ g) =
      toBoundedDerived f ≫ toBoundedDerived g := sorry

end CategoryTheory.NatTrans

namespace CategoryTheory.NatIso

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Preadditive A] [Abelian B] [HasDerivedCategory.{w} B]
  {F G : A ⥤ B} [F.Additive] [G.Additive]

/-- An additive natural isomorphism induces a natural isomorphism between the associated
functors `Kᵇ(A) ⟶ Dᵇ(B)`. -/
@[stacks 05T4 "bounded derived natural isomorphism"]
noncomputable def toBoundedDerived (e : F ≅ G) :
    F.toBoundedDerived ≅ G.toBoundedDerived :=
  Functor.isoWhiskerRight (Functor.Homotopy.Bounded.natIso e)
    (DerivedCategory.Bounded.Qh B)

/-- The forward map of the induced bounded natural isomorphism is the induced bounded natural
transformation. -/
@[simp]
theorem toBoundedDerived_hom (e : F ≅ G) :
    (toBoundedDerived e).hom = NatTrans.toBoundedDerived e.hom := sorry

/-- The inverse map of the induced bounded natural isomorphism is the induced bounded natural
transformation in the reverse direction. -/
@[simp]
theorem toBoundedDerived_inv (e : F ≅ G) :
    (toBoundedDerived e).inv = NatTrans.toBoundedDerived e.inv := sorry

/-- The forward component of the induced bounded natural isomorphism is obtained by localizing
the corresponding homotopy-category component. -/
@[simp]
theorem toBoundedDerived_hom_app
    (e : F ≅ G) (K : HomotopyCategory.Bounded A) :
    (toBoundedDerived e).hom.app K =
      (DerivedCategory.Bounded.Qh B).map
        ((Functor.Homotopy.Bounded.natIso e).hom.app K) := sorry

/-- The inverse component of the induced bounded natural isomorphism is obtained by localizing
the corresponding homotopy-category component. -/
@[simp]
theorem toBoundedDerived_inv_app
    (e : F ≅ G) (K : HomotopyCategory.Bounded A) :
    (toBoundedDerived e).inv.app K =
      (DerivedCategory.Bounded.Qh B).map
        ((Functor.Homotopy.Bounded.natIso e).inv.app K) := sorry

end CategoryTheory.NatIso
