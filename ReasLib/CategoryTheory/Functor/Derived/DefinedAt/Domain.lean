/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Domain

@[expose] public section

/-!
# Essential-Constancy Domains for Pointwise Derived Functors

Stacks' source notion of a derived functor being defined retains an essentially constant
localization-indexed diagram.  This leaf packages that stronger predicate as an object property
and a full subcategory, and provides canonical inclusions into Mathlib's weaker pointwise-existence
domains.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open ObjectProperty

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)

/-- The object property where the right-derived indexing diagram is essentially constant.  This
is stronger than `Functor.RightDerived.Definedness.property`, which records only pointwise existence. -/
@[stacks 05SC "essential-constancy domain of a right derived functor"]
abbrev Functor.RightDerived.DefinedAt.objects : ObjectProperty D :=
  fun X ↦ Functor.RightDerived.DefinedAt F S X

/-- The object property where the left-derived indexing diagram is essentially constant.  This is
stronger than `Functor.LeftDerived.Definedness.property`, which records only pointwise existence. -/
@[stacks 05SC "essential-constancy domain of a left derived functor"]
abbrev Functor.LeftDerived.DefinedAt.objects : ObjectProperty D :=
  fun X ↦ Functor.LeftDerived.DefinedAt F S X

/-- Right-derived essential constancy is invariant under isomorphisms of source objects. -/
instance Functor.RightDerived.DefinedAt.closedUnderIso :
    (Functor.RightDerived.DefinedAt.objects F S).IsClosedUnderIsomorphisms := sorry

/-- Left-derived essential constancy is invariant under isomorphisms of source objects. -/
instance Functor.LeftDerived.DefinedAt.closedUnderIso :
    (Functor.LeftDerived.DefinedAt.objects F S).IsClosedUnderIsomorphisms := sorry

/-- The full subcategory on which the right-derived indexing diagram is essentially constant. -/
@[stacks 05SC "essential-constancy subcategory for right derived values"]
abbrev Functor.RightDerived.DefinedAt.Domain :=
  (Functor.RightDerived.DefinedAt.objects F S).FullSubcategory

/-- The full subcategory on which the left-derived indexing diagram is essentially constant. -/
@[stacks 05SC "essential-constancy subcategory for left derived values"]
abbrev Functor.LeftDerived.DefinedAt.Domain :=
  (Functor.LeftDerived.DefinedAt.objects F S).FullSubcategory

/-- An object of the right essential-constancy subcategory automatically supplies the stronger
source-definedness instance. -/
instance Functor.RightDerived.DefinedAt.Domain.definedAt
    (X : Functor.RightDerived.DefinedAt.Domain F S) :
    Functor.RightDerived.DefinedAt F S X.obj := X.property

/-- An object of the left essential-constancy subcategory automatically supplies the stronger
source-definedness instance. -/
instance Functor.LeftDerived.DefinedAt.Domain.definedAt
    (X : Functor.LeftDerived.DefinedAt.Domain F S) :
    Functor.LeftDerived.DefinedAt F S X.obj := X.property

set_option backward.isDefEq.respectTransparency false in
/-- Essential constancy of the right-derived diagram implies Mathlib's pointwise-existence
property. -/
theorem Functor.RightDerived.DefinedAt.lePointwise :
    Functor.RightDerived.DefinedAt.objects F S ≤
      Functor.RightDerived.Definedness.property F S :=
  by
    intro X hX
    rcases hX.isEssentiallyConstant with ⟨c, i, σ, hfac⟩
    refine ⟨⟨⟨{ cocone := c, isColimit := ?_ }⟩⟩⟩
    refine { desc := fun s ↦ σ.section_ ≫ s.ι.app i, fac := ?_, uniq := ?_ }
    · intro s j
      rcases hfac j with ⟨k, ik, jk, hjk⟩
      calc
        c.ι.app j ≫ (σ.section_ ≫ s.ι.app i) =
            (c.ι.app j ≫ σ.section_ ≫
              (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F).map ik) ≫ s.ι.app k := by
          simp only [Category.assoc, s.w ik]
        _ = (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F).map jk ≫ s.ι.app k := by
          rw [← hjk]
        _ = s.ι.app j := s.w jk
    · intro s m hm
      calc
        m = (σ.section_ ≫ c.ι.app i) ≫ m := by rw [σ.id, Category.id_comp]
        _ = σ.section_ ≫ s.ι.app i := by rw [Category.assoc, hm i]

set_option backward.isDefEq.respectTransparency false in
/-- Essential constancy of the left-derived diagram implies Mathlib's pointwise-existence
property. -/
theorem Functor.LeftDerived.DefinedAt.lePointwise :
    Functor.LeftDerived.DefinedAt.objects F S ≤
      Functor.LeftDerived.Definedness.property F S :=
  by
    intro X hX
    rcases hX.isEssentiallyConstant with ⟨c, i, σ, hfac⟩
    refine ⟨⟨⟨{ cone := c, isLimit := ?_ }⟩⟩⟩
    refine { lift := fun s ↦ s.π.app i ≫ σ.retraction, fac := ?_, uniq := ?_ }
    · intro s j
      rcases hfac j with ⟨k, ki, kj, hkj⟩
      calc
        (s.π.app i ≫ σ.retraction) ≫ c.π.app j =
            s.π.app k ≫
              ((StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F).map ki ≫
                σ.retraction ≫ c.π.app j) := by
          simp only [← Category.assoc, s.w ki]
        _ = s.π.app k ≫ (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F).map kj := by
          rw [← hkj]
        _ = s.π.app j := s.w kj
    · intro s m hm
      have hσ : c.π.app i ≫ σ.retraction = 𝟙 c.pt := σ.id
      calc
        m = m ≫ (c.π.app i ≫ σ.retraction) := by rw [hσ, Category.comp_id]
        _ = s.π.app i ≫ σ.retraction := by rw [← Category.assoc, hm i]

/-- The canonical inclusion from the right essential-constancy domain into the pointwise-defined
domain.  It retains the underlying object and morphism. -/
def Functor.RightDerived.DefinedAt.Domain.toPointwise :
    Functor.RightDerived.DefinedAt.Domain F S ⥤ Functor.RightDerived.Definedness.Domain F S :=
  (Functor.RightDerived.DefinedAt.objects F S).ιOfLE
    (Functor.RightDerived.DefinedAt.lePointwise F S)

/-- The canonical inclusion from the left essential-constancy domain into the pointwise-defined
domain.  It retains the underlying object and morphism. -/
def Functor.LeftDerived.DefinedAt.Domain.toPointwise :
    Functor.LeftDerived.DefinedAt.Domain F S ⥤ Functor.LeftDerived.Definedness.Domain F S :=
  (Functor.LeftDerived.DefinedAt.objects F S).ιOfLE
    (Functor.LeftDerived.DefinedAt.lePointwise F S)

namespace Functor.RightDerived.DefinedAt.Domain.toPointwise

/-- The right-domain inclusion does not change the underlying source object. -/
@[simp]
theorem obj_obj (X : Functor.RightDerived.DefinedAt.Domain F S) :
    ((Functor.RightDerived.DefinedAt.Domain.toPointwise F S).obj X).obj = X.obj := sorry

/-- The right-domain inclusion retains the underlying source morphism. -/
@[simp]
theorem map_hom
    {X Y : Functor.RightDerived.DefinedAt.Domain F S} (f : X ⟶ Y) :
    ((Functor.RightDerived.DefinedAt.Domain.toPointwise F S).map f).hom = f.hom := sorry

end Functor.RightDerived.DefinedAt.Domain.toPointwise

namespace Functor.LeftDerived.DefinedAt.Domain.toPointwise

/-- The left-domain inclusion does not change the underlying source object. -/
@[simp]
theorem obj_obj (X : Functor.LeftDerived.DefinedAt.Domain F S) :
    ((Functor.LeftDerived.DefinedAt.Domain.toPointwise F S).obj X).obj = X.obj := sorry

/-- The left-domain inclusion retains the underlying source morphism. -/
@[simp]
theorem map_hom
    {X Y : Functor.LeftDerived.DefinedAt.Domain F S} (f : X ⟶ Y) :
    ((Functor.LeftDerived.DefinedAt.Domain.toPointwise F S).map f).hom = f.hom := sorry

end Functor.LeftDerived.DefinedAt.Domain.toPointwise



end CategoryTheory
