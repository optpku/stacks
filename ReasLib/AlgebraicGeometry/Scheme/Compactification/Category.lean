/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Compactification

/-- The defining conditions on an arrow `X ⟶ Xbar` over `S` that presents a
compactification: its interior map is a quasi-compact open immersion and `Xbar` is proper over
`S`. -/
class Is (S : Scheme.{u}) (j : Arrow (Over S)) : Prop where
  /-- The interior map is an open immersion. -/
  isOpenImmersion : IsOpenImmersion j.hom.left
  /-- The interior map is quasi-compact. -/
  quasiCompact : QuasiCompact j.hom.left
  /-- The ambient scheme is proper over the base. -/
  isProper : IsProper j.right.hom

/-- The defining compactification conditions, exposed as a conjunction. -/
theorem is_iff (S : Scheme.{u}) (j : Arrow (Over S)) :
    Is S j ↔ IsOpenImmersion j.hom.left ∧ QuasiCompact j.hom.left ∧ IsProper j.right.hom :=
  ⟨fun h ↦ ⟨h.isOpenImmersion, h.quasiCompact, h.isProper⟩,
    fun ⟨hi, hq, hp⟩ ↦ ⟨hi, hq, hp⟩⟩

namespace Is

/-- A compactification interior arrow carries its canonical open-immersion instance. -/
instance instIsOpenImmersion (S : Scheme.{u}) (j : Arrow (Over S)) [h : Is S j] :
    IsOpenImmersion j.hom.left := h.isOpenImmersion

/-- A compactification interior arrow carries its canonical quasi-compactness instance. -/
instance instQuasiCompact (S : Scheme.{u}) (j : Arrow (Over S)) [h : Is S j] :
    QuasiCompact j.hom.left := h.quasiCompact

/-- A compactification ambient scheme carries its canonical properness instance over the base. -/
instance instIsProper (S : Scheme.{u}) (j : Arrow (Over S)) [h : Is S j] :
    IsProper j.right.hom := h.isProper

end Is
end Compactification

/-- The category of compactifications over `S`, represented by arrows in `Over S` satisfying
the compactification conditions. -/
abbrev Compactification (S : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (Compactification.Is S)

namespace Compactification

/-- A bundled compactification carries its defining compactification instance. -/
instance instIs (S : Scheme.{u}) (X : Compactification S) : Is S X.obj := X.property

/-- Construct a compactification from a quasi-compact open immersion over `S` whose target is
proper over `S`. -/
def mk (S : Scheme.{u}) (X Xbar : Over S) (j : X ⟶ Xbar) [IsOpenImmersion j.left]
    [QuasiCompact j.left] [IsProper Xbar.hom] : Compactification S :=
  ⟨Arrow.mk j,
    { isOpenImmersion := inferInstanceAs (IsOpenImmersion j.left)
      quasiCompact := inferInstanceAs (QuasiCompact j.left)
      isProper := inferInstanceAs (IsProper Xbar.hom) }⟩

/-- The underlying arrow of `mk S X Xbar j` is the arrow determined by `j`. -/
theorem mk_obj (S : Scheme.{u}) (X Xbar : Over S) (j : X ⟶ Xbar) [IsOpenImmersion j.left]
    [QuasiCompact j.left] [IsProper Xbar.hom] :
    (mk S X Xbar j).obj = Arrow.mk j := rfl

/-- The functor sending a compactification to its open part over `S`. -/
def openPart (S : Scheme.{u}) : Compactification S ⥤ Over S :=
  ObjectProperty.ι (Is S) ⋙ Arrow.leftFunc

/-- The open-part functor returns the source of the underlying compactification arrow. -/
theorem openPart_obj (S : Scheme.{u}) (X : Compactification S) :
    (openPart S).obj X = X.obj.left := rfl

/-- The open-part functor sends a compactification morphism to its interior component. -/
theorem openPart_map (S : Scheme.{u}) {X Y : Compactification S} (f : X ⟶ Y) :
    (openPart S).map f = f.hom.left := rfl

/-- The functor sending a compactification to its proper part over `S`. -/
def properPart (S : Scheme.{u}) : Compactification S ⥤ Over S :=
  ObjectProperty.ι (Is S) ⋙ Arrow.rightFunc

/-- The proper-part functor returns the target of the underlying compactification arrow. -/
theorem properPart_obj (S : Scheme.{u}) (X : Compactification S) :
    (properPart S).obj X = X.obj.right := rfl

/-- The proper-part functor sends a compactification morphism to its ambient component. -/
theorem properPart_map (S : Scheme.{u}) {X Y : Compactification S} (f : X ⟶ Y) :
    (properPart S).map f = f.hom.right := rfl

/-- The functor from compactifications over `S` to their interior schemes. -/
def interior (S : Scheme.{u}) : Compactification S ⥤ Scheme :=
  openPart S ⋙ Over.forget S

/-- The interior functor returns the source scheme of a compactification. -/
theorem interior_obj (S : Scheme.{u}) (X : Compactification S) :
    (interior S).obj X = X.obj.left.left := rfl

/-- The interior functor sends a compactification morphism to its map on open parts. -/
theorem interior_map (S : Scheme.{u}) {X Y : Compactification S} (f : X ⟶ Y) :
    (interior S).map f = f.hom.left.left := rfl

/-- Morphisms of compactifications whose map on interiors is an isomorphism. -/
def interiorIsomorphisms (S : Scheme.{u}) : MorphismProperty (Compactification S) :=
  (MorphismProperty.isomorphisms Scheme).inverseImage (interior S)

/-- A compactification morphism belongs to `interiorIsomorphisms S` exactly when its interior
component is an isomorphism. -/
theorem interiorIsomorphisms_iff (S : Scheme.{u}) {X Y : Compactification S} (f : X ⟶ Y) :
    interiorIsomorphisms S f ↔ IsIso ((interior S).map f) := Iff.rfl

end Compactification
end Scheme
end AlgebraicGeometry
