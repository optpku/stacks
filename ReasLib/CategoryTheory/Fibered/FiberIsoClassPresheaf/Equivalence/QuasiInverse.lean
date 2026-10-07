module

public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.DiscreteTarget
public import ReasLib.CategoryTheory.Fibered.Setoids.Equivalence

/-!
# Fiber-class presheaves from explicit equivalences

Explicit quasi-inverse data for a based functor into a discrete fibration
identify source fiber isomorphism classes with target fiber objects. This leaf
owns the inverse natural transformation, the presheaf isomorphism, and their
same-universe computation API.
-/

@[expose] public section

universe u v uX vX vY

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace BasedFunctor.QuasiInverse

variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uX} C}
variable {F : X ⥤ᵇ Y}

/-- The fibre-class equivalences determined by explicit quasi-inverse data commute with
restriction in the base. -/
theorem fiberClassesIso.naturality
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered] [Functor.IsDiscreteFibration Y.p]
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (Functor.fiberIsoClassPresheaf X.p).map f ≫
        (fiberIsoClasses.equiv e (unop V)).toIso.hom =
      (fiberIsoClasses.equiv e (unop U)).toIso.hom ≫
        Y.p.fiberObjectPresheaf.map f := sorry

/-- The inverse fiber-class map determined by explicit quasi-inverse data commutes with
restriction in the base. -/
theorem fiberClassesInv.naturality
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered] [Functor.IsDiscreteFibration Y.p]
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    Y.p.fiberObjectPresheaf.map f ≫
        (fiberIsoClasses.equiv e (unop V)).toIso.inv =
      (fiberIsoClasses.equiv e (unop U)).toIso.inv ≫
        (Functor.fiberIsoClassPresheaf X.p).map f := sorry

/-- The inverse map from target fiber objects to source fiber classes selected by explicit
quasi-inverse data. Its components use the supplied inverse based functor. -/
noncomputable def fiberClassesInv
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered] [Functor.IsDiscreteFibration Y.p] :
    Y.p.fiberObjectPresheaf ⟶ Functor.fiberIsoClassPresheaf X.p where
  app U := (fiberIsoClasses.equiv e (unop U)).toIso.inv
  naturality := fun {_ _} f ↦ fiberClassesInv.naturality e f

/- Data audit: each component sends a target fiber object to the class of its image under the
explicit inverse fiber functor. Only its naturality field is deferred. -/

/-- The inverse map sends a target fiber object to the class of its image under the supplied
inverse fiber functor. -/
@[simp]
theorem fiberClassesInv.app
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered] [Functor.IsDiscreteFibration Y.p]
    (U : Cᵒᵖ) (y : Y.p.Fiber (unop U)) :
    e.fiberClassesInv.app U y =
      Quotient.mk'' ((e.inverse.fiberFunctor (unop U)).obj y) := sorry

/-- The canonical forward class-to-object map followed by the inverse selected by `e` is the
identity on source fiber classes. -/
theorem fiberClassesMap.comp_inv
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered] [Functor.IsDiscreteFibration Y.p] :
    BasedFunctor.fiberClassesMap F ≫ e.fiberClassesInv =
      𝟙 (Functor.fiberIsoClassPresheaf X.p) := sorry

/-- The inverse selected by `e` followed by the canonical forward class-to-object map is the
identity on target fiber objects. -/
theorem fiberClassesInv.comp_map
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered] [Functor.IsDiscreteFibration Y.p] :
    e.fiberClassesInv ≫ BasedFunctor.fiberClassesMap F =
      𝟙 Y.p.fiberObjectPresheaf := sorry

/-- Explicit quasi-inverse data identify the source fibre-class presheaf with the fibre-object
presheaf of a discrete target. Its forward and inverse component functions are determined by
`F` and `e.inverse`; only naturality and inverse laws are proof-valued. -/
noncomputable def fiberClassesIso
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered] [Functor.IsDiscreteFibration Y.p] :
    Functor.fiberIsoClassPresheaf X.p ≅ Y.p.fiberObjectPresheaf where
  hom := BasedFunctor.fiberClassesMap F
  inv := e.fiberClassesInv
  hom_inv_id := fiberClassesMap.comp_inv e
  inv_hom_id := fiberClassesInv.comp_map e

/-- The forward morphism of the explicit comparison is the canonical class-to-object map attached
to the forward based functor; it does not depend on quasi-inverse data. -/
@[simp]
theorem fiberClassesIso.hom_eq
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered] [Functor.IsDiscreteFibration Y.p] :
    e.fiberClassesIso.hom = BasedFunctor.fiberClassesMap F := sorry

/-- The inverse morphism of the explicit comparison is the separately named inverse map selected
by the quasi-inverse package. -/
@[simp]
theorem fiberClassesIso.inv_eq
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered] [Functor.IsDiscreteFibration Y.p] :
    e.fiberClassesIso.inv = e.fiberClassesInv := sorry

/-- On a represented source class, the explicit presheaf comparison applies the forward fibre
functor. -/
@[simp]
theorem fiberClassesIso.hom.app_mk
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered] [Functor.IsDiscreteFibration Y.p]
    (U : Cᵒᵖ) (x : X.p.Fiber (unop U)) :
    (e.fiberClassesIso).hom.app U (Quotient.mk'' x) =
      (F.fiberFunctor (unop U)).obj x := sorry

/-- The inverse explicit presheaf comparison takes the class of the image under the supplied
inverse based functor. -/
@[simp]
theorem fiberClassesIso.inv.app
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered] [Functor.IsDiscreteFibration Y.p]
    (U : Cᵒᵖ) (y : Y.p.Fiber (unop U)) :
    (e.fiberClassesIso).inv.app U y =
      Quotient.mk'' ((e.inverse.fiberFunctor (unop U)).obj y) := sorry

/-- The fibre-class comparison is independent of the unit, counit, and inverse chosen to witness
that the fixed forward based functor is an equivalence. -/
theorem fiberClassesIso.eq
    (e e' : BasedFunctor.QuasiInverse F) [X.p.IsFibered]
    [Functor.IsDiscreteFibration Y.p] :
    e.fiberClassesIso = e'.fiberClassesIso := sorry

end BasedFunctor.QuasiInverse

end CategoryTheory
