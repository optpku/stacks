/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# The 2-cell action of mapped cospans

This leaf owns the componentwise action of a pseudofunctor on a modification between walking-
cospan transformations.  Its three mapped `2`-morphism components are explicit; the naturality
and identity/composition equations are the modification-level API used by the hom functor.
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

namespace Hom

variable {ψ φ : CospanTransform f g f' g'}

namespace Implementation

/-- Mapping preserves the left generating modification square after inserting the canonical
pseudofunctor composition comparisons. -/
private theorem mapLeftNaturality
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) (P : B ⥤ᵖ B') :
    P.map₂ (left Γ) ▷ P.map f' ≫
        (CospanTransform.map φ P).leftIso.hom =
      (CospanTransform.map ψ P).leftIso.hom ≫
        P.map f ◁ P.map₂ (base Γ) := sorry

/-- Mapping preserves the right generating modification square after inserting the canonical
pseudofunctor composition comparisons. -/
private theorem mapRightNaturality
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) (P : B ⥤ᵖ B') :
    P.map₂ (right Γ) ▷ P.map g' ≫
        (CospanTransform.map φ P).rightIso.hom =
      (CospanTransform.map ψ P).rightIso.hom ≫
        P.map g ◁ P.map₂ (base Γ) := sorry

end Implementation

/-- Apply a pseudofunctor componentwise to a modification between cospan transformations. -/
@[stacks 0040 "map a bicategorical cospan modification by a pseudofunctor"]
def map (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) (P : B ⥤ᵖ B') :
    Pseudofunctor.StrongTrans.Hom
      (CospanTransform.map ψ P) (CospanTransform.map φ P) :=
  mk (P.map₂ (left Γ)) (P.map₂ (right Γ)) (P.map₂ (base Γ))
    (Implementation.mapLeftNaturality Γ P)
    (Implementation.mapRightNaturality Γ P)

/-- Mapping a cospan modification applies `P.map₂` to its left component. -/
@[simp]
theorem map.left
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) (P : B ⥤ᵖ B') :
    left (map Γ P) = P.map₂ (left Γ) := sorry

/-- Mapping a cospan modification applies `P.map₂` to its right component. -/
@[simp]
theorem map.right
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) (P : B ⥤ᵖ B') :
    right (map Γ P) = P.map₂ (right Γ) := sorry

/-- Mapping a cospan modification applies `P.map₂` to its common-target component. -/
@[simp]
theorem map.base
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) (P : B ⥤ᵖ B') :
    base (map Γ P) = P.map₂ (base Γ) := sorry

/-- Mapping preserves identity cospan modifications. -/
@[simp]
theorem map.id (ψ : CospanTransform f g f' g') (P : B ⥤ᵖ B') :
    map (id ψ) P = id (CospanTransform.map ψ P) := sorry

/-- Mapping preserves vertical composition of cospan modifications. -/
@[simp]
theorem map.comp
    {χ : CospanTransform f g f' g'}
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ)
    (Δ : Pseudofunctor.StrongTrans.Hom φ χ) (P : B ⥤ᵖ B') :
    map (comp Γ Δ) P = comp (map Γ P) (map Δ P) := sorry

end Hom

/- Data and axiom audit (mathlib 4.32): `Hom.map` stores the three mapped component cells
explicitly.  The two generating naturality squares and the identity/composition equations are
proof fields or proposition-valued interfaces; no `2`-morphism is chosen by `sorryAx`. -/

end CategoryTheory.Bicategory.CospanTransform
