/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Basic
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Map.Naturality.Minus

/-!
# Naturality of bounded-above induced functors

An additive natural transformation induces a natural transformation on bounded-above derived
categories. The construction is obtained by applying the bounded-above homotopy naturality API
and then localizing.
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
functors `K⁻(A) ⟶ D⁻(B)`. -/
@[stacks 05T4 "bounded-above derived natural transformation"]
noncomputable def toBoundedAboveDerived (f : F ⟶ G) :
    F.toBoundedAboveDerived ⟶ G.toBoundedAboveDerived :=
  Functor.whiskerRight (Functor.Homotopy.Minus.natTrans f)
    (DerivedCategory.Minus.Qh B)

/-- The component of `toBoundedAboveDerived f` is obtained by applying the bounded-above
localization functor to the corresponding homotopy-category component. -/
@[simp, stacks 05T4 "bounded-above derived natural transformation computation"]
theorem toBoundedAboveDerived_app (f : F ⟶ G) (K : HomotopyCategory.Minus A) :
    (toBoundedAboveDerived f).app K =
      (DerivedCategory.Minus.Qh B).map
        ((Functor.Homotopy.Minus.natTrans f).app K) := rfl

/-- The bounded-above derived action preserves identity natural transformations. -/
@[simp, stacks 05T4 "bounded-above derived natural transformation identity"]
theorem toBoundedAboveDerived_id :
    toBoundedAboveDerived (𝟙 F) = 𝟙 F.toBoundedAboveDerived := by
  apply NatTrans.ext
  funext K
  change (DerivedCategory.Minus.Qh B).map
    ((Functor.Homotopy.Minus.natTrans (𝟙 F)).app K) = 𝟙 _
  rw [← (DerivedCategory.Minus.Qh B).map_id]
  congr 1

/-- The bounded-above derived action preserves vertical composition. -/
@[simp, stacks 05T4 "bounded-above derived natural transformation composition"]
theorem toBoundedAboveDerived_comp (f : F ⟶ G) (g : G ⟶ H) :
    toBoundedAboveDerived (f ≫ g) =
      toBoundedAboveDerived f ≫ toBoundedAboveDerived g := by
  apply NatTrans.ext
  funext K
  change (DerivedCategory.Minus.Qh B).map
      ((Functor.Homotopy.Minus.natTrans (f ≫ g)).app K) =
    (DerivedCategory.Minus.Qh B).map ((Functor.Homotopy.Minus.natTrans f).app K) ≫
      (DerivedCategory.Minus.Qh B).map ((Functor.Homotopy.Minus.natTrans g).app K)
  rw [← (DerivedCategory.Minus.Qh B).map_comp]
  congr 1

end CategoryTheory.NatTrans

namespace CategoryTheory.NatIso

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Preadditive A] [Abelian B] [HasDerivedCategory.{w} B]
  {F G : A ⥤ B} [F.Additive] [G.Additive]

/-- An additive natural isomorphism induces a natural isomorphism between the associated
functors `K⁻(A) ⟶ D⁻(B)`. -/
@[stacks 05T4 "bounded-above derived natural isomorphism"]
noncomputable def toBoundedAboveDerived (e : F ≅ G) :
    F.toBoundedAboveDerived ≅ G.toBoundedAboveDerived :=
  Functor.isoWhiskerRight (Functor.Homotopy.Minus.natIso e)
    (DerivedCategory.Minus.Qh B)

/-- The forward map of the induced bounded-above natural isomorphism is the induced
bounded-above natural transformation. -/
@[simp]
theorem toBoundedAboveDerived_hom (e : F ≅ G) :
    (toBoundedAboveDerived e).hom =
      NatTrans.toBoundedAboveDerived e.hom := rfl

/-- The inverse map of the induced bounded-above natural isomorphism is the induced
bounded-above natural transformation in the reverse direction. -/
@[simp]
theorem toBoundedAboveDerived_inv (e : F ≅ G) :
    (toBoundedAboveDerived e).inv =
      NatTrans.toBoundedAboveDerived e.inv := rfl

/-- The forward component of the induced bounded-above natural isomorphism is obtained by
localizing the corresponding homotopy-category component. -/
@[simp]
theorem toBoundedAboveDerived_hom_app
    (e : F ≅ G) (K : HomotopyCategory.Minus A) :
    (toBoundedAboveDerived e).hom.app K =
      (DerivedCategory.Minus.Qh B).map
        ((Functor.Homotopy.Minus.natIso e).hom.app K) := rfl

/-- The inverse component of the induced bounded-above natural isomorphism is obtained by
localizing the corresponding homotopy-category component. -/
@[simp]
theorem toBoundedAboveDerived_inv_app
    (e : F ≅ G) (K : HomotopyCategory.Minus A) :
    (toBoundedAboveDerived e).inv.app K =
      (DerivedCategory.Minus.Qh B).map
        ((Functor.Homotopy.Minus.natIso e).inv.app K) := rfl

/-- The bounded-above derived lift preserves reflexive natural isomorphisms. -/
@[simp, stacks 05T4 "bounded-above derived natural isomorphism identity"]
theorem toBoundedAboveDerived_refl
    (F : A ⥤ B) [F.Additive] :
    toBoundedAboveDerived (Iso.refl F) =
      Iso.refl F.toBoundedAboveDerived := by
  apply Iso.ext
  change NatTrans.toBoundedAboveDerived (𝟙 F) = 𝟙 F.toBoundedAboveDerived
  exact NatTrans.toBoundedAboveDerived_id

/-- The bounded-above derived lift preserves symmetry of natural isomorphisms. -/
@[simp, stacks 05T4 "bounded-above derived natural isomorphism symmetry"]
theorem toBoundedAboveDerived_symm (e : F ≅ G) :
    toBoundedAboveDerived e.symm =
      (toBoundedAboveDerived e).symm := rfl

/-- The bounded-above derived lift preserves transitivity of natural isomorphisms. -/
@[simp, stacks 05T4 "bounded-above derived natural isomorphism composition"]
theorem toBoundedAboveDerived_trans
    {H : A ⥤ B} [H.Additive] (e : F ≅ G) (e' : G ≅ H) :
    toBoundedAboveDerived (e ≪≫ e') =
      toBoundedAboveDerived e ≪≫ toBoundedAboveDerived e' := by
  apply Iso.ext
  change NatTrans.toBoundedAboveDerived (e.hom ≫ e'.hom) =
    NatTrans.toBoundedAboveDerived e.hom ≫ NatTrans.toBoundedAboveDerived e'.hom
  exact NatTrans.toBoundedAboveDerived_comp e.hom e'.hom

end CategoryTheory.NatIso
