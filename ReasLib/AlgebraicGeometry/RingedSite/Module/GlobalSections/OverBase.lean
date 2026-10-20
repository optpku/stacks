module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.Linear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Derived.Category
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel
public import Mathlib.Algebra.Category.ModuleCat.Limits

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf.CommAlg
open SheafOfModules.RingedSite (unitModule)

noncomputable section

universe u v w

namespace SheafOfModules.CommAlg

variable {A : Type w} [CommRing A]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} A) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (O : Sheaf J (CommAlgCat.{w} A))

/-- A base-ring element as a global section of the structure module of `O`. -/
def baseRingSection (a : A) : (unitModule J (commRing O)).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ baseRingHom O U a)
    (fun {_ _} f ↦ map_baseRingHom O f a)

/-- Evaluating a base-ring section at `U` gives the objectwise algebra map. -/
theorem baseRingSection_apply (a : A) (U : Cᵒᵖ) :
    (baseRingSection O a).val U = baseRingHom O U a := rfl

variable [UnivLE.{u, w}]

/-- Global sections of module sheaves, computed as the limit of their local modules restricted
along the base-ring maps. -/
noncomputable def moduleGlobalSectionsOverBase :
    Modules.{w} O ⥤ ModuleCat.{w} A :=
  let diagrams : Modules.{w} O ⥤ (Cᵒᵖ ⥤ ModuleCat.{w} A) :=
    { obj := fun F ↦
        { obj := fun U ↦ (ModuleCat.restrictScalars (baseRingHom O U)).obj (F.val.obj U)
          map := fun {U V} f ↦ ModuleCat.ofHom
            (X := (ModuleCat.restrictScalars (baseRingHom O U)).obj (F.val.obj U))
            (Y := (ModuleCat.restrictScalars (baseRingHom O V)).obj (F.val.obj V))
            { toFun := F.val.map f
              map_add' := map_add _
              map_smul' := fun a x ↦ (F.val.map_smul f (baseRingHom O U a) x).trans (by
                rw [map_baseRingHom O f a]
                rfl) }
          map_id := fun U ↦ by
            ext x
            change F.val.map (𝟙 U) x = x
            simp
          map_comp := fun f g ↦ by ext x; exact F.val.map_comp_apply f g x }
      map := fun φ ↦
        { app := fun U ↦ (ModuleCat.restrictScalars (baseRingHom O U)).map (φ.val.app U)
          naturality := fun U V f ↦ by
            ext x
            exact PresheafOfModules.naturality_apply φ.val f x }
      map_id := fun F ↦ by ext U x; rfl
      map_comp := fun φ ψ ↦ by ext U x; rfl }
  diagrams ⋙ @lim _ _ _ _ (ModuleCat.hasLimitsOfShape (R := A))

/-- The value of base-valued global sections is the limit of the diagram of local modules. -/
theorem moduleGlobalSectionsOverBase_obj (F : Modules.{w} O) :
    (moduleGlobalSectionsOverBase O).obj F =
      limit (
        { obj := fun U ↦ (ModuleCat.restrictScalars (baseRingHom O U)).obj (F.val.obj U)
          map := fun {U V} f ↦ ModuleCat.ofHom
            (X := (ModuleCat.restrictScalars (baseRingHom O U)).obj (F.val.obj U))
            (Y := (ModuleCat.restrictScalars (baseRingHom O V)).obj (F.val.obj V))
            { toFun := F.val.map f
              map_add' := map_add _
              map_smul' := fun a x ↦ (F.val.map_smul f (baseRingHom O U a) x).trans (by
                rw [map_baseRingHom O f a]
                rfl) }
          map_id := fun U ↦ by
            ext x
            change F.val.map (𝟙 U) x = x
            simp
          map_comp := fun f g ↦ by ext x; exact F.val.map_comp_apply f g x } :
        Cᵒᵖ ⥤ ModuleCat.{w} A) := rfl

/-- Base-valued global sections form an additive functor. -/
noncomputable instance moduleGlobalSectionsOverBase_additive :
    (moduleGlobalSectionsOverBase O).Additive := sorry

/-- Base-valued global sections preserve monomorphisms. -/
noncomputable instance moduleGlobalSectionsOverBase_preservesMonomorphisms :
    (moduleGlobalSectionsOverBase O).PreservesMonomorphisms := sorry

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Derived base-valued global sections are obtained by applying global sections to the
specified K-injective model and localizing. -/
noncomputable def moduleDerivedGlobalSectionsOverBase
    [IsGrothendieckAbelian.{w} (Modules.{w} O)] :
    DerivedCategory (Modules.{w} O) ⥤ DerivedCategory (ModuleCat.{w} A) :=
  Functor.KInjectiveModel.derived (moduleGlobalSectionsOverBase O)

/-- Derived base-valued global sections evaluate the concrete K-injective derived functor. -/
theorem moduleDerivedGlobalSectionsOverBase_obj
    [IsGrothendieckAbelian.{w} (Modules.{w} O)]
    (F : DerivedCategory (Modules.{w} O)) :
    (moduleDerivedGlobalSectionsOverBase O).obj F =
      (Functor.KInjectiveModel.derived (moduleGlobalSectionsOverBase O)).obj F := rfl

end SheafOfModules.CommAlg

