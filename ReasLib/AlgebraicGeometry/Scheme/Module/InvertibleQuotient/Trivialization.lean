module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OverSections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Localization.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.InvertibleQuotient.Conormal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Open trivializations of invertible quotients

An open trivialization records only an isomorphism between the restricted
invertible target and the structure module.  Its sectionwise quotient and the
corresponding kernel--tensor-inverse comparison are derived from that
isomorphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace CategoryTheory.InvertibleQuotient

variable {X : Scheme.{u}} {E : X.Modules}

/-- A trivialization of the target of an invertible quotient on an open subset. -/
structure OpenTrivialization (q : InvertibleQuotient E) where
  /-- The open subset on which the quotient target is trivial. -/
  carrierOpen : X.Opens
  /-- The restricted quotient target is identified with the structure module. -/
  targetIso :
    (SheafOfModules.RingedSite.Localization.restriction
      (Scheme.schemeCommRingSheaf X) carrierOpen).obj q.object ≅
      𝟙_ (SheafOfModules (X.ringCatSheaf.over carrierOpen))

namespace OpenTrivialization

/-- Construct an open trivialization from its open subset and target isomorphism. -/
def ofIso (q : InvertibleQuotient E) (U : X.Opens)
    (e : (SheafOfModules.RingedSite.Localization.restriction
      (Scheme.schemeCommRingSheaf X) U).obj q.object ≅
        𝟙_ (SheafOfModules (X.ringCatSheaf.over U))) :
    OpenTrivialization q :=
  ⟨U, e⟩

/-- The quotient map restricted to the trivializing open. -/
noncomputable def quotientOver {q : InvertibleQuotient E}
    (t : OpenTrivialization q) :
    (SheafOfModules.RingedSite.Localization.restriction
      (Scheme.schemeCommRingSheaf X) t.carrierOpen).obj E ⟶
      SheafOfModules.unit (X.ringCatSheaf.over t.carrierOpen) :=
  (SheafOfModules.RingedSite.Localization.restriction
      (Scheme.schemeCommRingSheaf X) t.carrierOpen).map q.hom ≫ t.targetIso.hom ≫
    (SheafOfModules.RingedSite.unitIsoTensorUnit
      (J := (Opens.grothendieckTopology X).over t.carrierOpen)
      (𝒪 := X.sheaf.over t.carrierOpen)).inv

/-- The sectionwise quotient on a trivializing open. -/
noncomputable def quotient {q : InvertibleQuotient E}
    (t : OpenTrivialization q) :
    E.val.obj (op t.carrierOpen) →ₗ[X.ringCatSheaf.obj.obj (op t.carrierOpen)]
      X.ringCatSheaf.obj.obj (op t.carrierOpen) :=
  by
    let f := ((t.quotientOver).val.app
      (op (Over.mk (𝟙 t.carrierOpen)))).hom
    exact
      { toFun := fun x => f x
        map_add' := fun x y => f.map_add x y
        map_smul' := fun r x => f.map_smul r x }

/-- The chosen inverse of the restricted quotient target is canonically the structure
module on the trivializing open. -/
noncomputable def targetInverseIso {q : InvertibleQuotient E}
    (t : OpenTrivialization q) :
    (SheafOfModules.RingedSite.Localization.restriction
      (Scheme.schemeCommRingSheaf X) t.carrierOpen).obj
        (@isInvertibleObject.inverse X.Modules _ _ q.object q.isInvertible) ≅
      𝟙_ (SheafOfModules (X.ringCatSheaf.over t.carrierOpen)) :=
  by
    let F := SheafOfModules.RingedSite.Localization.restriction
      (Scheme.schemeCommRingSheaf X) t.carrierOpen
    let D := SheafOfModules (X.ringCatSheaf.over t.carrierOpen)
    let monoidalD := SheafOfModules.RingedSite.moduleMonoidalCategory
      ((Scheme.schemeCommRingSheaf X).over t.carrierOpen)
    let hF : @isInvertibleObject D _ monoidalD (F.obj q.object) :=
      @isInvertibleObject.map X.Modules _
        (SheafOfModules.RingedSite.moduleMonoidalCategory
          (Scheme.schemeCommRingSheaf X))
        D _ monoidalD F
        (SheafOfModules.RingedSite.Localization.restrictionMonoidal
          (Scheme.schemeCommRingSheaf X) t.carrierOpen)
        q.object q.isInvertible
    let p : @ExactPairing D _ monoidalD (F.obj q.object) (𝟙_ D) :=
      @ExactPairing.ofTensorInverse D _ monoidalD _ _
        ((@MonoidalCategoryStruct.rightUnitor D _ monoidalD.toMonoidalCategoryStruct
          (F.obj q.object)).trans t.targetIso)
        ((@MonoidalCategoryStruct.leftUnitor D _ monoidalD.toMonoidalCategoryStruct
          (F.obj q.object)).trans t.targetIso)
    exact
      (@isInvertibleObject.mapInverseIso X.Modules _
        (SheafOfModules.RingedSite.moduleMonoidalCategory
          (Scheme.schemeCommRingSheaf X))
        (SheafOfModules (X.ringCatSheaf.over t.carrierOpen)) _
        (SheafOfModules.RingedSite.moduleMonoidalCategory
          ((Scheme.schemeCommRingSheaf X).over t.carrierOpen)) F
        (SheafOfModules.RingedSite.Localization.restrictionMonoidal
          (Scheme.schemeCommRingSheaf X) t.carrierOpen)
        q.object q.isInvertible).symm ≪≫
        (@isInvertibleObject.inverseIso D _ monoidalD
          (F.obj q.object) hF _ p).symm

/-- Restriction to a trivializing open identifies the quotient conormal object with the
kernel of the resulting quotient onto the structure module. -/
noncomputable def conormalOverIso {q : InvertibleQuotient E}
    (t : OpenTrivialization q) :
    (SheafOfModules.RingedSite.Localization.restriction
      (Scheme.schemeCommRingSheaf X) t.carrierOpen).obj
        (@CategoryTheory.InvertibleQuotient.conormalObject X.Modules _
          (SheafOfModules.RingedSite.moduleMonoidalCategory
            (Scheme.schemeCommRingSheaf X)) _ _ E q) ≅
      kernel t.quotientOver :=
  by
    let F := SheafOfModules.RingedSite.Localization.restriction
      (Scheme.schemeCommRingSheaf X) t.carrierOpen
    exact
      (@Functor.Monoidal.μIso X.Modules _
        (SheafOfModules.RingedSite.moduleMonoidalCategory
          (Scheme.schemeCommRingSheaf X))
        (SheafOfModules (X.ringCatSheaf.over t.carrierOpen)) _
        (SheafOfModules.RingedSite.moduleMonoidalCategory
          ((Scheme.schemeCommRingSheaf X).over t.carrierOpen)) F
        (SheafOfModules.RingedSite.Localization.restrictionMonoidal
          (Scheme.schemeCommRingSheaf X) t.carrierOpen)
        (kernel q.hom)
        (@isInvertibleObject.inverse X.Modules _ _ q.object q.isInvertible)).symm ≪≫
        ((PreservesKernel.iso F q.hom ≪≫
          kernel.mapIso (F.map q.hom) t.quotientOver (Iso.refl _)
            (t.targetIso ≪≫
              (SheafOfModules.RingedSite.unitIsoTensorUnit
                (J := (Opens.grothendieckTopology X).over t.carrierOpen)
                (𝒪 := X.sheaf.over t.carrierOpen)).symm)
            (by
              simp only [quotientOver, Iso.trans_hom, Iso.symm_hom,
                Iso.refl_hom, Category.id_comp, F])) ⊗ᵢ
          t.targetInverseIso) ≪≫
        ρ_ _

/-- The conormal comparison on sections of a trivializing open. -/
noncomputable def conormalComparison {q : InvertibleQuotient E}
    (t : OpenTrivialization q) :
    (CategoryTheory.InvertibleQuotient.conormalObject q).val.obj
        (op t.carrierOpen) ≅
      ModuleCat.of (X.ringCatSheaf.obj.obj (op t.carrierOpen))
        (LinearMap.ker t.quotient) :=
  by
    let e :=
      (SheafOfModules.evaluation (X.ringCatSheaf.over t.carrierOpen)
          (op (Over.mk (𝟙 t.carrierOpen)))).mapIso t.conormalOverIso ≪≫
        PreservesKernel.iso
          (SheafOfModules.evaluation (X.ringCatSheaf.over t.carrierOpen)
            (op (Over.mk (𝟙 t.carrierOpen)))) t.quotientOver ≪≫
        ModuleCat.kernelIsoKer
          ((SheafOfModules.evaluation (X.ringCatSheaf.over t.carrierOpen)
            (op (Over.mk (𝟙 t.carrierOpen)))).map t.quotientOver)
    refine
      { hom := ModuleCat.ofHom
          { toFun := fun x =>
              ⟨(e.hom x).1, (e.hom x).2⟩
            map_add' := fun x y => by
              apply Subtype.ext
              change (e.hom (x + y)).1 = (e.hom x).1 + (e.hom y).1
              exact congrArg Subtype.val (e.hom.hom.map_add x y)
            map_smul' := fun r x => by
              apply Subtype.ext
              let r' : (X.ringCatSheaf.over t.carrierOpen).obj.obj
                  (op (Over.mk (𝟙 t.carrierOpen))) := r
              let x' : (SheafOfModules.evaluation
                (X.ringCatSheaf.over t.carrierOpen)
                (op (Over.mk (𝟙 t.carrierOpen)))).obj
                  ((SheafOfModules.RingedSite.Localization.restriction
                    (Scheme.schemeCommRingSheaf X) t.carrierOpen).obj
                    (@CategoryTheory.InvertibleQuotient.conormalObject X.Modules _
                      (SheafOfModules.RingedSite.moduleMonoidalCategory
                        (Scheme.schemeCommRingSheaf X)) _ _ E q)) := x
              change (e.hom (r' • x')).1 = r' • (e.hom x').1
              exact congrArg Subtype.val (e.hom.hom.map_smul r' x') }
        inv := ModuleCat.ofHom
          { toFun := fun x => e.inv ⟨x.1, x.2⟩
            map_add' := fun x y => e.inv.hom.map_add _ _
            map_smul' := fun r x => e.inv.hom.map_smul r _ }
        hom_inv_id := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          exact congrArg (fun f => f x) e.hom_inv_id
        inv_hom_id := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          apply Subtype.ext
          change (e.hom (e.inv x)).1 = x.1
          exact congrArg Subtype.val (congrArg (fun f => f x) e.inv_hom_id) }

/-- The open trivialization consists precisely of its carrier and target isomorphism. -/
theorem spec {q : InvertibleQuotient E} (t : OpenTrivialization q) :
    t = OpenTrivialization.ofIso q t.carrierOpen t.targetIso := sorry

end OpenTrivialization

end CategoryTheory.InvertibleQuotient
