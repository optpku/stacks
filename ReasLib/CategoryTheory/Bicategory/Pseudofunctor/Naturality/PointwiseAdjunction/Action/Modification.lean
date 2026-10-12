/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseAdjunction.Action.StrongTrans

/-!
# Modification action of pointwise adjunctions

This leaf maps modifications and functor-bicategory `2`-morphisms through the
canonical conjugate-mate construction used by pointwise adjunction actions.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor.StrongTrans

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Bicategory.{wD, vD} D]
variable {F G : Pseudofunctor B D}

namespace PointwiseAdjunction

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The component on adjunctions of a modification between pointwise-adjoint strong
transformations. Its right-adjoint component is the mate of the original modification
component. -/
@[stacks 0040 "component action on modifications between pointwise adjunctions"]
def mapAdj.modification.component
    {η θ : F ⟶ G} (hη : PointwiseAdjunction η)
    (hθ : PointwiseAdjunction θ)
    (Γ : StrongTrans.Modification η θ) (a : Bicategory.Adj B) :
    hη.mapAdj.app a ⟶ hθ.mapAdj.app a where
  τl := Γ.app a.obj
  τr := Bicategory.conjugateEquiv
    (hθ.app a.obj).adj (hη.app a.obj).adj (Γ.app a.obj)

/-- The mate-completed components of a modification satisfy naturality on adjunctions. -/
theorem mapAdj.modification.naturality
    {η θ : F ⟶ G} (hη : PointwiseAdjunction η)
    (hθ : PointwiseAdjunction θ)
    (Γ : StrongTrans.Modification η θ)
    {a b : Bicategory.Adj B} (f : a ⟶ b) :
    F.mapAdj.map f ◁ mapAdj.modification.component hη hθ Γ b ≫
        (hθ.mapAdj.naturality f).hom =
      (hη.mapAdj.naturality f).hom ≫
        mapAdj.modification.component hη hθ Γ a ▷
          G.mapAdj.map f := sorry

/-- Map a modification between pointwise-adjoint strong transformations to a modification
between their induced actions on adjunctions. -/
@[stacks 0040 "modification action between pointwise adjunctions"]
def mapAdj.modification
    {η θ : F ⟶ G} (hη : PointwiseAdjunction η)
    (hθ : PointwiseAdjunction θ)
    (Γ : StrongTrans.Modification η θ) :
    StrongTrans.Modification hη.mapAdj hθ.mapAdj where
  app := mapAdj.modification.component hη hθ Γ
  naturality := mapAdj.modification.naturality hη hθ Γ

/-- Components of a mapped modification are the canonical mate pairs. -/
@[simp]
theorem mapAdj.modification.app
    {η θ : F ⟶ G} (hη : PointwiseAdjunction η)
    (hθ : PointwiseAdjunction θ)
    (Γ : StrongTrans.Modification η θ) (a : Bicategory.Adj B) :
    (mapAdj.modification hη hθ Γ).app a =
      mapAdj.modification.component hη hθ Γ a := sorry

/-- The left-adjoint component of a mapped modification is the original component. -/
@[simp]
theorem mapAdj.modification.app.τl
    {η θ : F ⟶ G} (hη : PointwiseAdjunction η)
    (hθ : PointwiseAdjunction θ)
    (Γ : StrongTrans.Modification η θ) (a : Bicategory.Adj B) :
    ((mapAdj.modification hη hθ Γ).app a).τl =
      Γ.app a.obj := sorry

/-- The right-adjoint component of a mapped modification is the conjugate mate of the
original component. -/
@[simp]
theorem mapAdj.modification.app.τr
    {η θ : F ⟶ G} (hη : PointwiseAdjunction η)
    (hθ : PointwiseAdjunction θ)
    (Γ : StrongTrans.Modification η θ) (a : Bicategory.Adj B) :
    ((mapAdj.modification hη hθ Γ).app a).τr =
      Bicategory.conjugateEquiv
        (hθ.app a.obj).adj (hη.app a.obj).adj
        (Γ.app a.obj) := sorry

/-- Mapping pointwise-adjoint modifications preserves identity modifications. -/
@[simp]
theorem mapAdj.modification.id
    {η : F ⟶ G} (h : PointwiseAdjunction η) :
    mapAdj.modification h h (StrongTrans.Modification.id η) =
      StrongTrans.Modification.id h.mapAdj := sorry

/-- Mapping pointwise-adjoint modifications preserves vertical composition. -/
@[simp]
theorem mapAdj.modification.vcomp
    {η θ ι : F ⟶ G} (hη : PointwiseAdjunction η)
    (hθ : PointwiseAdjunction θ) (hι : PointwiseAdjunction ι)
    (Γ : StrongTrans.Modification η θ)
    (Δ : StrongTrans.Modification θ ι) :
    mapAdj.modification hη hι
        (StrongTrans.Modification.vcomp Γ Δ) =
      StrongTrans.Modification.vcomp
        (mapAdj.modification hη hθ Γ)
        (mapAdj.modification hθ hι Δ) := sorry

/-- Map a functor-bicategory `2`-morphism between pointwise-adjoint strong transformations. -/
@[stacks 0040 "2-morphism action between pointwise adjunctions"]
def mapAdj.map₂
    {η θ : F ⟶ G} (hη : PointwiseAdjunction η)
    (hθ : PointwiseAdjunction θ) (Γ : η ⟶ θ) :
  hη.mapAdj ⟶ hθ.mapAdj :=
  ⟨mapAdj.modification hη hθ Γ.as⟩

/-- The underlying modification of a mapped functor-bicategory `2`-morphism. -/
@[simp]
theorem mapAdj.map₂.as
    {η θ : F ⟶ G} (hη : PointwiseAdjunction η)
    (hθ : PointwiseAdjunction θ) (Γ : η ⟶ θ) :
    (mapAdj.map₂ hη hθ Γ).as =
      mapAdj.modification hη hθ Γ.as := sorry

/-- The left-adjoint component of a mapped functor-bicategory `2`-morphism. -/
@[simp]
theorem mapAdj.map₂.app.τl
    {η θ : F ⟶ G} (hη : PointwiseAdjunction η)
    (hθ : PointwiseAdjunction θ) (Γ : η ⟶ θ)
    (a : Bicategory.Adj B) :
    ((mapAdj.map₂ hη hθ Γ).as.app a).τl =
      Γ.as.app a.obj := sorry

/-- The right-adjoint component of a mapped functor-bicategory `2`-morphism is the
conjugate mate of its original component. -/
@[simp]
theorem mapAdj.map₂.app.τr
    {η θ : F ⟶ G} (hη : PointwiseAdjunction η)
    (hθ : PointwiseAdjunction θ) (Γ : η ⟶ θ)
    (a : Bicategory.Adj B) :
    ((mapAdj.map₂ hη hθ Γ).as.app a).τr =
      Bicategory.conjugateEquiv
        (hθ.app a.obj).adj (hη.app a.obj).adj
        (Γ.as.app a.obj) := sorry

/-- Mapping functor-bicategory `2`-morphisms preserves identities. -/
@[simp]
theorem mapAdj.map₂.id
    {η : F ⟶ G} (h : PointwiseAdjunction η) :
    mapAdj.map₂ h h (𝟙 η) = 𝟙 h.mapAdj := sorry

/-- Mapping functor-bicategory `2`-morphisms preserves vertical composition. -/
@[simp]
theorem mapAdj.map₂.comp
    {η θ ι : F ⟶ G} (hη : PointwiseAdjunction η)
    (hθ : PointwiseAdjunction θ) (hι : PointwiseAdjunction ι)
    (Γ : η ⟶ θ) (Δ : θ ⟶ ι) :
    mapAdj.map₂ hη hι (Γ ≫ Δ) =
      mapAdj.map₂ hη hθ Γ ≫ mapAdj.map₂ hθ hι Δ := sorry

/-- The two mapped directions of an invertible `2`-cell cancel. -/
private theorem Implementation.mapIso.hom_inv_id
    {η θ : F ⟶ G} (hη : PointwiseAdjunction η)
    (hθ : PointwiseAdjunction θ) (Γ : η ≅ θ) :
    mapAdj.map₂ hη hθ Γ.hom ≫ mapAdj.map₂ hθ hη Γ.inv =
      𝟙 hη.mapAdj := sorry

/-- The two mapped directions of an invertible `2`-cell cancel in the reverse
order. -/
private theorem Implementation.mapIso.inv_hom_id
    {η θ : F ⟶ G} (hη : PointwiseAdjunction η)
    (hθ : PointwiseAdjunction θ) (Γ : η ≅ θ) :
    mapAdj.map₂ hθ hη Γ.inv ≫ mapAdj.map₂ hη hθ Γ.hom =
      𝟙 hθ.mapAdj := sorry

/-- Map an invertible `2`-cell between pointwise-adjoint strong
transformations to an isomorphism between their induced adjunction actions.

This also compares different chosen pointwise adjunction structures on the
same strong transformation by taking `Γ := Iso.refl _`. -/
@[stacks 0040 "isomorphism action between pointwise adjunctions"]
def mapAdj.mapIso
    {η θ : F ⟶ G} (hη : PointwiseAdjunction η)
    (hθ : PointwiseAdjunction θ) (Γ : η ≅ θ) :
    hη.mapAdj ≅ hθ.mapAdj where
  hom := mapAdj.map₂ hη hθ Γ.hom
  inv := mapAdj.map₂ hθ hη Γ.inv
  hom_inv_id := Implementation.mapIso.hom_inv_id hη hθ Γ
  inv_hom_id := Implementation.mapIso.inv_hom_id hη hθ Γ

/-- The forward morphism of `mapAdj.mapIso` is the mapped forward cell. -/
@[simp]
theorem mapAdj.mapIso.hom
    {η θ : F ⟶ G} (hη : PointwiseAdjunction η)
    (hθ : PointwiseAdjunction θ) (Γ : η ≅ θ) :
    (mapAdj.mapIso hη hθ Γ).hom =
      mapAdj.map₂ hη hθ Γ.hom := sorry

/-- The inverse morphism of `mapAdj.mapIso` is the mapped inverse cell. -/
@[simp]
theorem mapAdj.mapIso.inv
    {η θ : F ⟶ G} (hη : PointwiseAdjunction η)
    (hθ : PointwiseAdjunction θ) (Γ : η ≅ θ) :
    (mapAdj.mapIso hη hθ Γ).inv =
      mapAdj.map₂ hθ hη Γ.inv := sorry

/- Data audit (mathlib 4.32): `mapAdj.modification.component` uses
`Bicategory.conjugateEquiv` for its explicit right-adjoint component.
`mapAdj.mapIso` retains both mapped directions explicitly. Any `sorryAx` is
confined to modification naturality, functoriality, and inverse laws. -/

end PointwiseAdjunction

end Pseudofunctor.StrongTrans

end CategoryTheory
