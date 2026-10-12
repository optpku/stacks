/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Modification
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom-category functoriality of cospan mapping

This leaf assembles the hom-category functor induced by componentwise mapping and the induced
map on isomorphisms.  Its object and morphism readouts are kept beside the assembly so consumers
of this layer get the complete hom-category API without importing coherence comparisons.
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

/-- Applying a pseudofunctor to transformations and modifications is functorial on each
hom-category between two fixed cospans. -/
@[stacks 0040 "hom functor for mapping bicategorical cospans"]
def map.functor (P : B ⥤ᵖ B') :
    CospanTransform f g f' g' ⥤
      CospanTransform (P.map f) (P.map g) (P.map f') (P.map g') where
  obj ψ := map ψ P
  map Γ := Hom.map Γ P
  map_id ψ := Hom.map.id ψ P
  map_comp Γ Δ := Hom.map.comp Γ Δ P

/-- The object action of `map.functor` is componentwise mapping of cospan transformations. -/
@[simp]
theorem map.functor.obj
    (P : B ⥤ᵖ B') (ψ : CospanTransform f g f' g') :
    (map.functor P).obj ψ = map ψ P := sorry

/-- The morphism action of `map.functor` is componentwise mapping of cospan modifications. -/
@[simp]
theorem map.functor.map_apply
    (P : B ⥤ᵖ B') {ψ φ : CospanTransform f g f' g'}
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    (map.functor P).map Γ = Hom.map Γ P := sorry

/-- Apply a pseudofunctor to an isomorphism between cospan transformations. -/
@[stacks 0040 "map an isomorphism of bicategorical cospan transformations"]
def map.iso
    {ψ φ : CospanTransform f g f' g'} (e : ψ ≅ φ) (P : B ⥤ᵖ B') :
    map ψ P ≅ map φ P :=
  (map.functor P).mapIso e

/-- The forward component of a mapped cospan-transformation isomorphism is the mapped
modification. -/
@[simp]
theorem map.iso.hom
    {ψ φ : CospanTransform f g f' g'} (e : ψ ≅ φ) (P : B ⥤ᵖ B') :
    (map.iso e P).hom = Hom.map e.hom P := sorry

/-- The inverse component of a mapped cospan-transformation isomorphism is the mapped
modification. -/
@[simp]
theorem map.iso.inv
    {ψ φ : CospanTransform f g f' g'} (e : ψ ≅ φ) (P : B ⥤ᵖ B') :
    (map.iso e P).inv = Hom.map e.inv P := sorry

/- Data and axiom audit (mathlib 4.32): `map.functor` has explicit object and morphism actions
from the two preceding owners; `map.iso` is the canonical image of an isomorphism under that
functor.  Deferred content is confined to functor and category-law propositions. -/

end CategoryTheory.Bicategory.CospanTransform
