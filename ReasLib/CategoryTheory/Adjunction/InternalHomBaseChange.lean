module

public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison
public import ReasLib.CategoryTheory.Monoidal.Closed.OplaxMonoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change for internal Homs

Given a square of left adjoints and a tensor comparison for the horizontal pullback, the right
mate of the square applied to an internal Hom can be followed by the pullback/internal-Hom
comparison.  This is the categorical owner of the derived internal-Hom base-change map; geometric
and derived models only supply the six functors and their adjunctions.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace CategoryTheory.Adjunction.InternalHomBaseChange

variable {C : Type u₁} [Category.{v₁} C]
variable {C' : Type u₂} [Category.{v₂} C']
variable {D : Type u₃} [Category.{v₃} D]
variable {D' : Type u₄} [Category.{v₄} D']

variable [MonoidalCategory C] [BraidedCategory C]
variable [MonoidalCategory C'] [BraidedCategory C']

variable {h : C ⥤ C'} {g : D ⥤ D'} {f : D ⥤ C} {f' : D' ⥤ C'}
variable {Rf : C ⥤ D} {Rf' : C' ⥤ D'}

/-- Remark 20.42.14 (08I4), explicit-owner form: the pointwise internal-Hom base-change map
attached to a square of left adjoints and chosen closed structures on its horizontal categories.
-/
@[stacks 08I4 "explicit internal-Hom base-change map"]
noncomputable def mapOf
    (H : MonoidalClosed C) (H' : MonoidalClosed C')
    (adj_f : f ⊣ Rf) (adj_f' : f' ⊣ Rf')
    (tensorIso : ∀ A B : C, h.obj (A ⊗ B) ≅ h.obj A ⊗ h.obj B)
    (squareIso : g ⋙ f' ≅ f ⋙ h)
    (K L : C) :
    g.obj (Rf.obj ((ihomOf H K).obj L)) ⟶
      Rf'.obj ((ihomOf H' (h.obj K)).obj (h.obj L)) :=
  derivedBaseChangeMap f f' g h Rf Rf' adj_f adj_f' squareIso
      ((ihomOf H K).obj L) ≫
    Rf'.map (Functor.PullbackInternalHom.comparisonOf H H' h tensorIso K L)

/-- The adjunction transpose of the explicit-owner base-change map is the square comparison,
the first counit, and the explicit pullback/internal-Hom comparison. -/
@[stacks 08I4 "explicit internal-Hom base-change specification"]
theorem mapOf_spec
    (H : MonoidalClosed C) (H' : MonoidalClosed C')
    (adj_f : f ⊣ Rf) (adj_f' : f' ⊣ Rf')
    (tensorIso : ∀ A B : C, h.obj (A ⊗ B) ≅ h.obj A ⊗ h.obj B)
    (squareIso : g ⋙ f' ≅ f ⋙ h)
    (K L : C) :
    (adj_f'.homEquiv
        (g.obj (Rf.obj ((ihomOf H K).obj L)))
        ((ihomOf H' (h.obj K)).obj (h.obj L))).symm
        (mapOf H H' adj_f adj_f' tensorIso squareIso K L) =
      squareIso.hom.app (Rf.obj ((ihomOf H K).obj L)) ≫
        h.map (adj_f.counit.app ((ihomOf H K).obj L)) ≫
        Functor.PullbackInternalHom.comparisonOf H H' h tensorIso K L := sorry

section Typeclass

variable [MonoidalClosed C] [MonoidalClosed C']

/-- Remark 20.42.14 (08I4), generic owner: the internal-Hom base-change map attached to a square
of left adjoints, their right adjunctions, and the tensor comparison for `h`. -/
@[stacks 08I4 "internal-Hom base-change map"]
noncomputable def map
    (adj_f : f ⊣ Rf) (adj_f' : f' ⊣ Rf')
    (tensorIso : ∀ A B : C, h.obj (A ⊗ B) ≅ h.obj A ⊗ h.obj B)
    (squareIso : g ⋙ f' ≅ f ⋙ h)
    (K L : C) :
    g.obj (Rf.obj ((ihom K).obj L)) ⟶
      Rf'.obj ((ihom (h.obj K)).obj (h.obj L)) :=
  mapOf (inferInstance : MonoidalClosed C) (inferInstance : MonoidalClosed C')
    adj_f adj_f' tensorIso squareIso K L

/-- The adjunction transpose of `map` is the square comparison, the first counit, and the
pullback/internal-Hom comparison in that order. -/
@[stacks 08I4 "internal-Hom base-change specification"]
theorem map_spec
    (adj_f : f ⊣ Rf) (adj_f' : f' ⊣ Rf')
    (tensorIso : ∀ A B : C, h.obj (A ⊗ B) ≅ h.obj A ⊗ h.obj B)
    (squareIso : g ⋙ f' ≅ f ⋙ h)
    (K L : C) :
    (adj_f'.homEquiv
        (g.obj (Rf.obj ((ihom K).obj L)))
        ((ihom (h.obj K)).obj (h.obj L))).symm
        (map adj_f adj_f' tensorIso squareIso K L) =
      squareIso.hom.app (Rf.obj ((ihom K).obj L)) ≫
        h.map (adj_f.counit.app ((ihom K).obj L)) ≫
        Functor.PullbackInternalHom.comparison h tensorIso K L := sorry

/-- The same base-change map when the horizontal pullback is strong monoidal.  The tensor
comparison is then supplied by the canonical oplax structure and is not a user-level argument. -/
@[stacks 08I4 "strong-monoidal internal-Hom base-change map"]
noncomputable def map_monoidal
    [h.Monoidal]
    (adj_f : f ⊣ Rf) (adj_f' : f' ⊣ Rf')
    (squareIso : g ⋙ f' ≅ f ⋙ h) (K L : C) :
    g.obj (Rf.obj ((ihom K).obj L)) ⟶
      Rf'.obj ((ihom (h.obj K)).obj (h.obj L)) :=
  map adj_f adj_f'
    (fun A B ↦ asIso (Functor.OplaxMonoidal.δ h A B)) squareIso K L

/-- The adjunction-transpose specification of `map_monoidal`. -/
@[stacks 08I4 "strong-monoidal internal-Hom base-change specification"]
theorem map_monoidal_spec
    [h.Monoidal]
    (adj_f : f ⊣ Rf) (adj_f' : f' ⊣ Rf')
    (squareIso : g ⋙ f' ≅ f ⋙ h) (K L : C) :
    (adj_f'.homEquiv
        (g.obj (Rf.obj ((ihom K).obj L)))
        ((ihom (h.obj K)).obj (h.obj L))).symm
        (map_monoidal adj_f adj_f' squareIso K L) =
      squareIso.hom.app (Rf.obj ((ihom K).obj L)) ≫
        h.map (adj_f.counit.app ((ihom K).obj L)) ≫
        Functor.OplaxMonoidal.InternalHom.comparison h K L := sorry

end Typeclass

end CategoryTheory.Adjunction.InternalHomBaseChange
