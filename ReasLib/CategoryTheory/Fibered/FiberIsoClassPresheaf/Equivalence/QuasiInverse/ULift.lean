/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Equivalence.QuasiInverse

/-!
# Universe-lifted fiber-class presheaves from explicit equivalences

This leaf lifts the explicit quasi-inverse comparison of fiber isomorphism
classes with discrete-fibration objects to a chosen common universe.
-/

@[expose] public section

universe w u v uX vX uY vY

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace BasedFunctor.QuasiInverse

variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {F : X ⥤ᵇ Y}

private theorem fiberClassesMap_ulift_app
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered]
    [Functor.IsDiscreteFibration Y.p] (U : Cᵒᵖ) :
    (BasedFunctor.fiberClassesMap.ulift.{w} F).app U =
      (Equiv.ulift.trans
        ((fiberIsoClasses.equiv e (unop U)).trans Equiv.ulift.symm)).toIso.hom := by
  ext q
  rcases q with ⟨q⟩
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-- The lifted fibre-class equivalences from explicit quasi-inverse data commute with base
restriction in any chosen common ambient universe. -/
theorem fiberClassesIso.ulift.naturality
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered]
    [Functor.IsDiscreteFibration Y.p] {U V : Cᵒᵖ} (f : U ⟶ V) :
    (Functor.fiberIsoClassPresheaf X.p ⋙
        (CategoryTheory.uliftFunctor.{max w uX uY, uX} :
          Type uX ⥤ Type (max w uX uY))).map f ≫
        (Equiv.ulift.trans
          ((fiberIsoClasses.equiv e (unop V)).trans Equiv.ulift.symm)).toIso.hom =
      (Equiv.ulift.trans
          ((fiberIsoClasses.equiv e (unop U)).trans Equiv.ulift.symm)).toIso.hom ≫
        (Y.p.fiberObjectPresheaf ⋙
          (CategoryTheory.uliftFunctor.{max w uX uY, uY} :
            Type uY ⥤ Type (max w uX uY))).map f := by
  rw [← fiberClassesMap_ulift_app e U, ← fiberClassesMap_ulift_app e V]
  exact (BasedFunctor.fiberClassesMap.ulift.{w} F).naturality f

/-- The lifted inverse selected by explicit quasi-inverse data commutes with restriction in the
base. -/
theorem fiberClassesInv.ulift.naturality
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered]
    [Functor.IsDiscreteFibration Y.p] {U V : Cᵒᵖ} (f : U ⟶ V) :
    (Y.p.fiberObjectPresheaf ⋙
        (CategoryTheory.uliftFunctor.{max w uX uY, uY} :
          Type uY ⥤ Type (max w uX uY))).map f ≫
        (Equiv.ulift.trans
          ((fiberIsoClasses.equiv e (unop V)).trans Equiv.ulift.symm)).toIso.inv =
      (Equiv.ulift.trans
          ((fiberIsoClasses.equiv e (unop U)).trans Equiv.ulift.symm)).toIso.inv ≫
        (Functor.fiberIsoClassPresheaf X.p ⋙
          (CategoryTheory.uliftFunctor.{max w uX uY, uX} :
            Type uX ⥤ Type (max w uX uY))).map f := by
  let α :
      (Functor.fiberIsoClassPresheaf X.p ⋙
        (uliftFunctor.{max w uX uY, uX} : Type uX ⥤ Type (max w uX uY))) ≅
      (Y.p.fiberObjectPresheaf ⋙
        (uliftFunctor.{max w uX uY, uY} : Type uY ⥤ Type (max w uX uY))) :=
    NatIso.ofComponents
      (fun U ↦ (Equiv.ulift.trans
        ((fiberIsoClasses.equiv e (unop U)).trans Equiv.ulift.symm)).toIso)
      (fun f ↦ fiberClassesIso.ulift.naturality e f)
  exact α.inv.naturality f

/-- The inverse from lifted target fiber objects to lifted source fiber classes selected by
explicit quasi-inverse data. -/
noncomputable def fiberClassesInv.ulift
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered]
    [Functor.IsDiscreteFibration Y.p] :
    (Y.p.fiberObjectPresheaf ⋙
        (CategoryTheory.uliftFunctor.{max w uX uY, uY} :
          Type uY ⥤ Type (max w uX uY))) ⟶
      (Functor.fiberIsoClassPresheaf X.p ⋙
        (CategoryTheory.uliftFunctor.{max w uX uY, uX} :
          Type uX ⥤ Type (max w uX uY))) where
  app U := (Equiv.ulift.trans
    ((fiberIsoClasses.equiv e (unop U)).trans Equiv.ulift.symm)).toIso.inv
  naturality := fun {_ _} f ↦ fiberClassesInv.ulift.naturality e f

/- Data audit: the component function uses only `ULift` and the supplied inverse fiber functor;
its naturality follows from the forward comparison. -/

/-- On a lifted target fiber object, the lifted inverse returns the lifted class of its image
under the supplied inverse fiber functor. -/
@[simp]
theorem fiberClassesInv.ulift.app
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered]
    [Functor.IsDiscreteFibration Y.p] (U : Cᵒᵖ) (y : Y.p.Fiber (unop U)) :
    (BasedFunctor.QuasiInverse.fiberClassesInv.ulift.{w} e).app U (ULift.up y) =
      ULift.up (Quotient.mk'' ((e.inverse.fiberFunctor (unop U)).obj y)) := by
  rfl

/-- The lifted canonical forward map followed by the lifted inverse selected by `e` is the
identity on lifted source fiber classes. -/
theorem fiberClassesMap.ulift.comp_inv
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered]
    [Functor.IsDiscreteFibration Y.p] :
    BasedFunctor.fiberClassesMap.ulift.{w} F ≫
        BasedFunctor.QuasiInverse.fiberClassesInv.ulift.{w} e =
      𝟙 (Functor.fiberIsoClassPresheaf X.p ⋙
        (CategoryTheory.uliftFunctor.{max w uX uY, uX} :
          Type uX ⥤ Type (max w uX uY))) := by
  apply NatTrans.ext
  funext U
  rw [NatTrans.comp_app, NatTrans.id_app, fiberClassesMap_ulift_app e]
  exact (Equiv.ulift.trans
    ((fiberIsoClasses.equiv e (unop U)).trans Equiv.ulift.symm)).toIso.hom_inv_id

/-- The lifted inverse selected by `e` followed by the lifted canonical forward map is the
identity on lifted target fiber objects. -/
theorem fiberClassesInv.ulift.comp_map
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered]
    [Functor.IsDiscreteFibration Y.p] :
    BasedFunctor.QuasiInverse.fiberClassesInv.ulift.{w} e ≫
        BasedFunctor.fiberClassesMap.ulift.{w} F =
      𝟙 (Y.p.fiberObjectPresheaf ⋙
        (CategoryTheory.uliftFunctor.{max w uX uY, uY} :
          Type uY ⥤ Type (max w uX uY))) := by
  apply NatTrans.ext
  funext U
  rw [NatTrans.comp_app, NatTrans.id_app, fiberClassesMap_ulift_app e]
  exact (Equiv.ulift.trans
    ((fiberIsoClasses.equiv e (unop U)).trans Equiv.ulift.symm)).toIso.inv_hom_id

/-- Explicit quasi-inverse data identify fiber classes and target fiber objects after lifting to
any chosen common ambient universe. -/
noncomputable def fiberClassesIso.ulift
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered]
    [Functor.IsDiscreteFibration Y.p] :
    (Functor.fiberIsoClassPresheaf X.p ⋙
        (CategoryTheory.uliftFunctor.{max w uX uY, uX} :
          Type uX ⥤ Type (max w uX uY))) ≅
      (Y.p.fiberObjectPresheaf ⋙
        (CategoryTheory.uliftFunctor.{max w uX uY, uY} :
          Type uY ⥤ Type (max w uX uY))) where
  hom := BasedFunctor.fiberClassesMap.ulift.{w} F
  inv := BasedFunctor.QuasiInverse.fiberClassesInv.ulift.{w} e
  hom_inv_id := fiberClassesMap.ulift.comp_inv e
  inv_hom_id := fiberClassesInv.ulift.comp_map e

/-- The forward morphism of the lifted comparison is the canonical lifted class-to-object map. -/
@[simp]
theorem fiberClassesIso.ulift.hom_eq
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered]
    [Functor.IsDiscreteFibration Y.p] :
    (BasedFunctor.QuasiInverse.fiberClassesIso.ulift.{w} e).hom =
      BasedFunctor.fiberClassesMap.ulift.{w} F := by
  rfl

/-- The inverse morphism of the lifted comparison is the separately named lifted inverse map. -/
@[simp]
theorem fiberClassesIso.ulift.inv_eq
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered]
    [Functor.IsDiscreteFibration Y.p] :
    (BasedFunctor.QuasiInverse.fiberClassesIso.ulift.{w} e).inv =
      BasedFunctor.QuasiInverse.fiberClassesInv.ulift.{w} e := by
  rfl

/-- On a lifted represented class, the explicit comparison applies the forward fiber functor. -/
@[simp]
theorem fiberClassesIso.ulift.hom.app_mk
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered]
    [Functor.IsDiscreteFibration Y.p] (U : Cᵒᵖ) (x : X.p.Fiber (unop U)) :
    (BasedFunctor.QuasiInverse.fiberClassesIso.ulift.{w} e).hom.app U
        (ULift.up (Quotient.mk'' x)) =
      ULift.up ((F.fiberFunctor (unop U)).obj x) := by
  rfl

/-- The inverse lifted comparison uses the inverse contained in the explicit coherence data. -/
@[simp]
theorem fiberClassesIso.ulift.inv.app
    (e : BasedFunctor.QuasiInverse F) [X.p.IsFibered]
    [Functor.IsDiscreteFibration Y.p] (U : Cᵒᵖ) (y : Y.p.Fiber (unop U)) :
    (BasedFunctor.QuasiInverse.fiberClassesIso.ulift.{w} e).inv.app U (ULift.up y) =
      ULift.up (Quotient.mk'' ((e.inverse.fiberFunctor (unop U)).obj y)) := by
  rfl

/-- The lifted comparison is independent of the explicit quasi-inverse coherence package. -/
theorem fiberClassesIso.ulift.eq
    (e e' : BasedFunctor.QuasiInverse F) [X.p.IsFibered]
    [Functor.IsDiscreteFibration Y.p] :
    BasedFunctor.QuasiInverse.fiberClassesIso.ulift.{w} e =
      BasedFunctor.QuasiInverse.fiberClassesIso.ulift.{w} e' := by
  apply Iso.ext
  rfl

end BasedFunctor.QuasiInverse

end CategoryTheory
