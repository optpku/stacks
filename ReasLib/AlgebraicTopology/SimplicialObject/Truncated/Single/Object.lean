module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Truncated simplicial objects concentrated in one degree

This leaf owns the objectwise and morphism-level construction of `Truncated.concentrated B k`,
together with its top object.  Functoriality and universal Hom descriptions are separate layers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open SimplexCategory
open scoped SimplexCategory.Truncated Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

namespace concentrated.raw

variable [HasZeroObject A]

/-- The object assignment of the `k`-truncated simplicial object concentrated in degree `k`.
It is `B` in top degree and the zero object in every lower degree. -/
@[stacks 018Y "concentrated object assignment"]
def obj (B : A) (k : ℕ) : (SimplexCategory.Truncated k)ᵒᵖ → A :=
  fun X ↦ if X.unop.1.len = k then B else ⊥_ A

/-- The concentrated object assignment evaluates to `B` at every object of top degree. -/
@[stacks 018Y "concentrated object top computation"]
theorem obj.eq_top (B : A) (k : ℕ)
    (X : (SimplexCategory.Truncated k)ᵒᵖ) (hX : X.unop.1.len = k) :
    obj B k X = B := sorry

/-- A truncated simplex whose length is the truncation bound has the standard top simplex as
its underlying simplex. -/
@[stacks 018Y "top truncated simplex identification"]
theorem eq_mk_of_len_eq {k : ℕ} {X : (SimplexCategory.Truncated k)ᵒᵖ}
    (hX : X.unop.1.len = k) : X.unop.1 = ⦋k⦌ := sorry

/-- Transport a morphism between top-degree truncated simplices to an endomorphism of the
standard top simplex. -/
@[stacks 018Y "concentrated top endomorphism"]
def topEndomorphism {k : ℕ} {X Y : (SimplexCategory.Truncated k)ᵒᵖ}
    (f : X ⟶ Y) (hX : X.unop.1.len = k) (hY : Y.unop.1.len = k) : ⦋k⦌ ⟶ ⦋k⦌ :=
  eqToHom (SimplexCategory.ext hY).symm ≫ f.unop.hom ≫ eqToHom (SimplexCategory.ext hX)

/-- The morphism assignment of the concentrated truncated simplicial object. The identity
endomorphism in top degree acts by the transported identity of `B`; every other morphism acts
by zero. -/
@[stacks 018Y "concentrated morphism assignment"]
def map (B : A) (k : ℕ) {X Y : (SimplexCategory.Truncated k)ᵒᵖ}
    (f : X ⟶ Y) : obj B k X ⟶ obj B k Y :=
  if hX : X.unop.1.len = k then
    if hY : Y.unop.1.len = k then
      if topEndomorphism f hX hY = 𝟙 ⦋k⦌ then
        eqToHom (if_pos hX) ≫ eqToHom (if_pos hY).symm
      else 0
    else 0
  else 0

/-- The concentrated morphism assignment preserves identities. -/
@[stacks 018Y "concentrated identity computation"]
theorem map.id (B : A) (k : ℕ)
    (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    map B k (𝟙 X) = 𝟙 (obj B k X) := sorry

/-- The concentrated morphism assignment preserves composition. -/
@[stacks 018Y "concentrated composition computation"]
theorem map.comp (B : A) (k : ℕ)
    {X Y Z : (SimplexCategory.Truncated k)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map B k (f ≫ g) = map B k f ≫ map B k g := sorry

end concentrated.raw

section Construction

variable [HasZeroObject A]

/-- The `k`-truncated simplicial object concentrated in degree `k` with value `B`.
At the top degree it has value `B`; at all other degrees it is the zero object.
Only the identity endomorphism of the top simplex acts nontrivially. -/
@[stacks 018Y "concentrated truncated simplicial object"]
def concentrated (B : A) (k : ℕ) : SimplicialObject.Truncated A k where
  obj := concentrated.raw.obj B k
  map f := concentrated.raw.map B k f
  map_id X := concentrated.raw.map.id B k X
  map_comp f g := concentrated.raw.map.comp B k f g

/-- The object assignment of `concentrated B k` is `concentrated.raw.obj B k`. -/
@[simp, stacks 018Y "concentrated object projection"]
theorem concentrated.obj_eq (B : A) (k : ℕ)
    (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    (concentrated B k).obj X = concentrated.raw.obj B k X := sorry

/-- The simplex-morphism assignment of `concentrated B k` is `concentrated.raw.map B k`. -/
@[simp, stacks 018Y "concentrated map projection"]
theorem concentrated.map_eq (B : A) (k : ℕ)
    {X Y : (SimplexCategory.Truncated k)ᵒᵖ} (f : X ⟶ Y) :
    (concentrated B k).map f = concentrated.raw.map B k f := sorry

/-- The concentrated truncated simplicial object has value `B` at the top degree. -/
@[simp, stacks 018Y "concentrated top object"]
theorem concentrated.obj_top (B : A) (k : ℕ) :
    (concentrated B k).obj (op ⦋k, le_rfl⦌ₖ) = B := sorry

end Construction

namespace concentrated

/-- The top object of the `k`-truncated simplex category. -/
@[stacks 018Y "top object of the truncated simplex category"]
abbrev top (k : ℕ) : SimplexCategory.Truncated k := ⦋k, le_rfl⦌ₖ

end concentrated

end CategoryTheory.SimplicialObject.Truncated
