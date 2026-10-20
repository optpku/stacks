module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Functoriality
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Swap.Transform
import Mathlib.Tactic.CrossRefAttribute

/-!
# Mapping swapped bicategorical cospans

Swapping the two endpoints of a cospan transformation or modification commutes with applying
a pseudofunctor. The functor-level statement packages both compatibilities for downstream use.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

universe w v u w' v' u'

namespace CategoryTheory.Bicategory.CospanTransform

variable {B : Type u} [Bicategory.{w, v} B]
variable {B' : Type u'} [Bicategory.{w', v'} B']
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- Applying a pseudofunctor after swapping a cospan transformation agrees with swapping the
componentwise mapped transformation. -/
@[simp, stacks 0040 "mapping commutes with swapping bicategorical cospans"]
theorem swap.map (ψ : CospanTransform f g f' g') (P : B ⥤ᵖ B') :
    CospanTransform.map (CospanTransform.swap ψ) P =
      CospanTransform.swap (CospanTransform.map ψ P) := sorry

namespace Hom

variable {ψ φ : CospanTransform f g f' g'}

/-- Applying a pseudofunctor to a swapped modification agrees, after the canonical endpoint
transports, with swapping the componentwise mapped modification. -/
theorem swap.map
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) (P : B ⥤ᵖ B') :
    Hom.map (Hom.swap Γ) P =
      eqToHom (CospanTransform.swap.map ψ P) ≫
        Hom.swap (Hom.map Γ P) ≫
          eqToHom (CospanTransform.swap.map φ P).symm := sorry

end Hom

/-- The swap functor commutes with the functor induced by applying a pseudofunctor. -/
theorem swap.map.functor (P : B ⥤ᵖ B') :
    swap.functor (f := f) (g := g) (f' := f') (g' := g') ⋙
        CospanTransform.map.functor
          (f := g) (g := f) (f' := g') (g' := f') P =
      CospanTransform.map.functor
          (f := f) (g := g) (f' := f') (g' := g') P ⋙
        swap.functor
          (f := P.map f) (g := P.map g)
          (f' := P.map f') (g' := P.map g') := sorry

end CategoryTheory.Bicategory.CospanTransform
