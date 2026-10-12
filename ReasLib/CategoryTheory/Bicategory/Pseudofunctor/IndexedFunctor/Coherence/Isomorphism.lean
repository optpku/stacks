/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Composition.Basic

/-!
# Isomorphisms of indexed functors
-/

@[expose] public section

universe uC vC uD vD uE vE uI vI uJ vJ uF vF uG vG uH vH uM vM uN vN

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

namespace IndexedFunctor

variable {u : C ⥤ D}
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vG, uG}}

/-- The component maps of an isomorphism of indexed functors satisfy the forward inverse
identity. -/
theorem isoApp_hom_inv_id
    {H K : IndexedFunctor u F G} (e : H ≅ K) (U : C) :
    e.hom.app U ≫ e.inv.app U = 𝟙 (H.app U) := sorry

/-- The component maps of an isomorphism of indexed functors satisfy the inverse forward
identity. -/
theorem isoApp_inv_hom_id
    {H K : IndexedFunctor u F G} (e : H ≅ K) (U : C) :
    e.inv.app U ≫ e.hom.app U = 𝟙 (K.app U) := sorry

/-- An isomorphism of indexed functors induces a natural isomorphism between its component
functors over every base object. -/
def isoApp
    {H K : IndexedFunctor u F G} (e : H ≅ K) (U : C) :
    H.app U ≅ K.app U where
  hom := e.hom.app U
  inv := e.inv.app U
  hom_inv_id := isoApp_hom_inv_id e U
  inv_hom_id := isoApp_inv_hom_id e U

/-- The forward map of `isoApp` is the corresponding component of the forward indexed
modification. -/
@[simp]
theorem isoApp_hom
    {H K : IndexedFunctor u F G} (e : H ≅ K) (U : C) :
    (isoApp e U).hom = e.hom.app U := sorry

/-- The inverse map of `isoApp` is the corresponding component of the inverse indexed
modification. -/
@[simp]
theorem isoApp_inv
    {H K : IndexedFunctor u F G} (e : H ≅ K) (U : C) :
    (isoApp e U).inv = e.inv.app U := sorry

/-- Inverse compatibility with reindexing follows from forward compatibility for a family of
component natural isomorphisms. -/
theorem isoMk_inv_naturality
    {H K : IndexedFunctor u F G}
    (e : ∀ U : C, H.app U ≅ K.app U)
    (naturality :
      ∀ {U V : C} (f : V ⟶ U)
        (x : F.obj (LocallyDiscrete.mk (Opposite.op U))),
        (H.naturality f).hom.app x ≫
            (G.map (u.map f).op.toLoc).toFunctor.map ((e U).hom.app x) =
          (e V).hom.app ((F.map f.op.toLoc).toFunctor.obj x) ≫
            (K.naturality f).hom.app x)
    {U V : C} (f : V ⟶ U)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    (K.naturality f).hom.app x ≫
        (G.map (u.map f).op.toLoc).toFunctor.map ((e U).inv.app x) =
      (e V).inv.app ((F.map f.op.toLoc).toFunctor.obj x) ≫
        (H.naturality f).hom.app x := sorry

namespace Implementation

/-- The implementation-level forward indexed modification underlying `mkIso`. -/
def isoMkHom
    {H K : IndexedFunctor u F G}
    (e : ∀ U : C, H.app U ≅ K.app U)
    (naturality :
      ∀ {U V : C} (f : V ⟶ U)
        (x : F.obj (LocallyDiscrete.mk (Opposite.op U))),
        (H.naturality f).hom.app x ≫
            (G.map (u.map f).op.toLoc).toFunctor.map ((e U).hom.app x) =
          (e V).hom.app ((F.map f.op.toLoc).toFunctor.obj x) ≫
            (K.naturality f).hom.app x) :
    H ⟶ K where
  app U := (e U).hom
  naturality f x := naturality f x

/-- The implementation-level inverse indexed modification underlying `mkIso`. -/
def isoMkInv
    {H K : IndexedFunctor u F G}
    (e : ∀ U : C, H.app U ≅ K.app U)
    (naturality :
      ∀ {U V : C} (f : V ⟶ U)
        (x : F.obj (LocallyDiscrete.mk (Opposite.op U))),
        (H.naturality f).hom.app x ≫
            (G.map (u.map f).op.toLoc).toFunctor.map ((e U).hom.app x) =
          (e V).hom.app ((F.map f.op.toLoc).toFunctor.obj x) ≫
            (K.naturality f).hom.app x) :
    K ⟶ H where
  app U := (e U).inv
  naturality f x := isoMk_inv_naturality e naturality f x

/-- The implementation-level forward and inverse indexed modifications assembled from component
isomorphisms compose to the identity on the source. -/
theorem isoMkHom_isoMkInv
    {H K : IndexedFunctor u F G}
    (e : ∀ U : C, H.app U ≅ K.app U)
    (naturality :
      ∀ {U V : C} (f : V ⟶ U)
        (x : F.obj (LocallyDiscrete.mk (Opposite.op U))),
        (H.naturality f).hom.app x ≫
            (G.map (u.map f).op.toLoc).toFunctor.map ((e U).hom.app x) =
          (e V).hom.app ((F.map f.op.toLoc).toFunctor.obj x) ≫
            (K.naturality f).hom.app x) :
    isoMkHom e naturality ≫ isoMkInv e naturality = 𝟙 H := sorry

/-- The implementation-level inverse and forward indexed modifications assembled from component
isomorphisms compose to the identity on the target. -/
theorem isoMkInv_isoMkHom
    {H K : IndexedFunctor u F G}
    (e : ∀ U : C, H.app U ≅ K.app U)
    (naturality :
      ∀ {U V : C} (f : V ⟶ U)
        (x : F.obj (LocallyDiscrete.mk (Opposite.op U))),
        (H.naturality f).hom.app x ≫
            (G.map (u.map f).op.toLoc).toFunctor.map ((e U).hom.app x) =
          (e V).hom.app ((F.map f.op.toLoc).toFunctor.obj x) ≫
            (K.naturality f).hom.app x) :
    isoMkInv e naturality ≫ isoMkHom e naturality = 𝟙 K := sorry

end Implementation

/-- Construct an isomorphism of indexed functors from component natural isomorphisms and their
forward compatibility with reindexing. The inverse compatibility is automatic. -/
def mkIso
    {H K : IndexedFunctor u F G}
    (e : ∀ U : C, H.app U ≅ K.app U)
    (naturality :
      ∀ {U V : C} (f : V ⟶ U)
        (x : F.obj (LocallyDiscrete.mk (Opposite.op U))),
        (H.naturality f).hom.app x ≫
            (G.map (u.map f).op.toLoc).toFunctor.map ((e U).hom.app x) =
          (e V).hom.app ((F.map f.op.toLoc).toFunctor.obj x) ≫
            (K.naturality f).hom.app x) :
    H ≅ K where
  hom := Implementation.isoMkHom e naturality
  inv := Implementation.isoMkInv e naturality
  hom_inv_id := Implementation.isoMkHom_isoMkInv e naturality
  inv_hom_id := Implementation.isoMkInv_isoMkHom e naturality

/-- The component natural isomorphism of `mkIso` is the supplied component. -/
@[simp]
theorem isoApp_mkIso
    {H K : IndexedFunctor u F G}
    (e : ∀ U : C, H.app U ≅ K.app U)
    (naturality :
      ∀ {U V : C} (f : V ⟶ U)
        (x : F.obj (LocallyDiscrete.mk (Opposite.op U))),
        (H.naturality f).hom.app x ≫
            (G.map (u.map f).op.toLoc).toFunctor.map ((e U).hom.app x) =
          (e V).hom.app ((F.map f.op.toLoc).toFunctor.obj x) ≫
            (K.naturality f).hom.app x)
    (U : C) :
    isoApp (mkIso e naturality) U = e U := sorry


end IndexedFunctor

end Pseudofunctor.LocallyDiscreteOpToCat

end CategoryTheory
