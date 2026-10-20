/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Basic
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Map.Naturality.Plus

/-!
# Naturality of bounded-below induced functors

An additive natural transformation induces a natural transformation on bounded-below derived
categories. The construction is obtained by applying the bounded-below homotopy naturality API
and then localizing.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.NatTrans

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Preadditive 𝒜]

variable [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
variable {F G H : 𝒜 ⥤ ℬ} [F.Additive] [G.Additive] [H.Additive]

/-- An additive natural transformation induces a natural transformation between the associated
functors `K⁺(𝒜) ⟶ D⁺(ℬ)`. -/
@[stacks 05T4 "bounded-below derived natural transformation"]
noncomputable def toBoundedBelowDerived (f : F ⟶ G) :
    F.toBoundedBelowDerived ⟶ G.toBoundedBelowDerived :=
  Functor.whiskerRight (Functor.Homotopy.Plus.natTrans f)
    (DerivedCategory.Plus.Qh : HomotopyCategory.Plus ℬ ⥤ DerivedCategory.Plus ℬ)

/-- The component of `toBoundedBelowDerived f` is obtained by applying the bounded-below
localization functor to the corresponding homotopy-category component. -/
@[simp, stacks 05T4 "bounded-below derived natural transformation computation"]
theorem toBoundedBelowDerived_app (f : F ⟶ G) (K : HomotopyCategory.Plus 𝒜) :
    (toBoundedBelowDerived f).app K =
      DerivedCategory.Plus.Qh.map
        ((Functor.Homotopy.Plus.natTrans f).app K) := sorry

/-- The bounded-below derived lift preserves identity natural transformations. -/
@[simp, stacks 05T4 "bounded-below derived natural transformation identity"]
theorem toBoundedBelowDerived_id :
    toBoundedBelowDerived (𝟙 F) = 𝟙 F.toBoundedBelowDerived := sorry

/-- The bounded-below derived lift preserves composition of natural transformations. -/
@[simp, stacks 05T4 "bounded-below derived natural transformation composition"]
theorem toBoundedBelowDerived_comp (f : F ⟶ G) (g : G ⟶ H) :
    toBoundedBelowDerived (f ≫ g) =
      toBoundedBelowDerived f ≫ toBoundedBelowDerived g := sorry

namespace toBoundedBelowDerived

/-- An invertible additive transformation induces an invertible transformation on bounded-below
derived categories. -/
@[stacks 05T4 "isomorphism preservation for bounded-below derived naturality"]
noncomputable instance isIso (f : F ⟶ G) [IsIso f] :
    IsIso (NatTrans.toBoundedBelowDerived f) := sorry

end toBoundedBelowDerived

end CategoryTheory.NatTrans

namespace CategoryTheory.NatIso

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Preadditive A] [Abelian B] [HasDerivedCategory.{w} B]
  {F G : A ⥤ B} [F.Additive] [G.Additive]

/-- An additive natural isomorphism induces a natural isomorphism between the associated
functors `K⁺(A) ⟶ D⁺(B)`. -/
@[stacks 05T4 "bounded-below derived natural isomorphism"]
noncomputable def toBoundedBelowDerived (e : F ≅ G) :
    F.toBoundedBelowDerived ≅ G.toBoundedBelowDerived :=
  Functor.isoWhiskerRight (Functor.Homotopy.Plus.natIso e)
    (DerivedCategory.Plus.Qh : HomotopyCategory.Plus B ⥤ DerivedCategory.Plus B)

/-- The forward map of the induced bounded-below natural isomorphism is the induced
bounded-below natural transformation. -/
@[simp]
theorem toBoundedBelowDerived_hom (e : F ≅ G) :
    (toBoundedBelowDerived e).hom =
      NatTrans.toBoundedBelowDerived e.hom := sorry

/-- The inverse map of the induced bounded-below natural isomorphism is the induced
bounded-below natural transformation in the reverse direction. -/
@[simp]
theorem toBoundedBelowDerived_inv (e : F ≅ G) :
    (toBoundedBelowDerived e).inv =
      NatTrans.toBoundedBelowDerived e.inv := sorry

/-- The forward component of the induced bounded-below natural isomorphism is obtained by
localizing the corresponding homotopy-category component. -/
@[simp]
theorem toBoundedBelowDerived_hom_app
    (e : F ≅ G) (K : HomotopyCategory.Plus A) :
    (toBoundedBelowDerived e).hom.app K =
      DerivedCategory.Plus.Qh.map
        ((Functor.Homotopy.Plus.natIso e).hom.app K) := sorry

/-- The inverse component of the induced bounded-below natural isomorphism is obtained by
localizing the corresponding homotopy-category component. -/
@[simp]
theorem toBoundedBelowDerived_inv_app
    (e : F ≅ G) (K : HomotopyCategory.Plus A) :
    (toBoundedBelowDerived e).inv.app K =
      DerivedCategory.Plus.Qh.map
        ((Functor.Homotopy.Plus.natIso e).inv.app K) := sorry

/-- The bounded-below derived lift preserves reflexive natural isomorphisms. -/
@[simp, stacks 05T4 "bounded-below derived natural isomorphism identity"]
theorem toBoundedBelowDerived_refl
    (F : A ⥤ B) [F.Additive] :
    toBoundedBelowDerived (Iso.refl F) =
      Iso.refl F.toBoundedBelowDerived := sorry

/-- The bounded-below derived lift preserves symmetry of natural isomorphisms. -/
@[simp, stacks 05T4 "bounded-below derived natural isomorphism symmetry"]
theorem toBoundedBelowDerived_symm (e : F ≅ G) :
    toBoundedBelowDerived e.symm =
      (toBoundedBelowDerived e).symm := sorry

/-- The bounded-below derived lift preserves transitivity of natural isomorphisms. -/
@[simp, stacks 05T4 "bounded-below derived natural isomorphism composition"]
theorem toBoundedBelowDerived_trans
    {H : A ⥤ B} [H.Additive] (e : F ≅ G) (e' : G ≅ H) :
    toBoundedBelowDerived (e ≪≫ e') =
      toBoundedBelowDerived e ≪≫ toBoundedBelowDerived e' := sorry

end CategoryTheory.NatIso
