module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.RingTheory.Ideal.FiniteGeneration.Family
public import stacks_project.Chap52.Lemma_52_6_16_ExtendedCech

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf.CommAlg
open RingedSite
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace RingedSite.Hom

variable {A : Type w} [CommRing A]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} A) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (O : Sheaf J (CommAlgCat.{w} A))
variable [UnivLE.{u, w}] [UnivLE.{max u v, w}]

/-- The objectwise base-ring maps form a cone over the underlying structure-ring presheaf. -/
theorem baseRingCone_naturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    ((Functor.const Cᵒᵖ).obj (RingCat.of A)).map f ≫
        RingCat.ofHom (SheafOfModules.CommAlg.baseRingHom O V) =
      RingCat.ofHom (SheafOfModules.CommAlg.baseRingHom O U) ≫
        (ofCommRingSheaf J (commRing O)).structureSheaf.obj.map f := sorry

/-- The cone of base-ring maps from `A` to the local rings of an `A`-algebra sheaf. -/
noncomputable def baseRingCone :
    Cone (ofCommRingSheaf J (commRing O)).structureSheaf.obj where
  pt := RingCat.of A
  π :=
    { app := fun U ↦ RingCat.ofHom (SheafOfModules.CommAlg.baseRingHom O U)
      naturality := fun {_ _} f ↦ baseRingCone_naturality O f }

/-- Multiplication on the global-sections ring of a commutative algebra sheaf is commutative. -/
theorem globalSections_mul_comm
    (a b : globalSectionsRing (ofCommRingSheaf J (commRing O))) :
    a * b = b * a := sorry

/-- The canonical commutative-ring structure on global sections of a commutative algebra sheaf. -/
noncomputable instance globalSectionsCommRing :
    CommRing (globalSectionsRing (ofCommRingSheaf J (commRing O))) where
  toRing := inferInstance
  mul_comm := globalSections_mul_comm O

/-- The ring map `A ⟶ Γ(C, O)` induced by the `A`-algebra structure on `O`. -/
noncomputable def baseRingToGlobalSections :
    A →+* globalSectionsRing (ofCommRingSheaf J (commRing O)) :=
  (limit.lift _ (baseRingCone O)).hom

/-- The map `A ⟶ Γ(C, O)` evaluates to the given base-ring map on every object of the site. -/
theorem baseRingToGlobalSections_apply (a : A) (U : Cᵒᵖ) :
    ((limit.π (ofCommRingSheaf J (commRing O)).structureSheaf.obj U).hom)
        (baseRingToGlobalSections O a) =
      SheafOfModules.CommAlg.baseRingHom O U a := sorry

/-- Global sections of `O`-modules, regarded canonically as `A`-modules. -/
noncomputable abbrev moduleGlobalSectionsOverBase :
    ModuleCat.{w} (ofCommRingSheaf J (commRing O)) ⥤ _root_.ModuleCat.{w} A :=
  moduleGlobalSectionsFunctor (ofCommRingSheaf J (commRing O)) ⋙
    _root_.ModuleCat.restrictScalars (baseRingToGlobalSections O)

/-- On objects, `moduleGlobalSectionsOverBase` is global sections followed by restriction of
scalars along `A ⟶ Γ(C, O)`. -/
theorem moduleGlobalSectionsOverBase_obj
    (F : ModuleCat.{w} (ofCommRingSheaf J (commRing O))) :
    (moduleGlobalSectionsOverBase O).obj F =
      (_root_.ModuleCat.restrictScalars (baseRingToGlobalSections O)).obj
        ((moduleGlobalSectionsFunctor
          (ofCommRingSheaf J (commRing O))).obj F) := sorry

/-- The `A`-module-valued global-sections functor is additive. -/
noncomputable instance moduleGlobalSectionsOverBase_additive :
    (moduleGlobalSectionsOverBase O).Additive := sorry

/-- The `A`-module-valued global-sections functor preserves monomorphisms. -/
noncomputable instance moduleGlobalSectionsOverBase_preservesMonomorphisms :
    (moduleGlobalSectionsOverBase O).PreservesMonomorphisms := sorry

/-- Global sections of `O`-modules, regarded canonically as complexes of `A`-modules. -/
noncomputable abbrev moduleDerivedGlobalSectionsOverBase
    [IsGrothendieckAbelian (ModuleCat.{w} (ofCommRingSheaf J (commRing O)))] :
    ModuleDerived.{w} (ofCommRingSheaf J (commRing O)) ⥤
      DerivedCategory (_root_.ModuleCat.{w} A) :=
  moduleDerivedGlobalSections (ofCommRingSheaf J (commRing O)) ⋙
    _root_.CategoryTheory.ModuleCat.derivedRestrictionOfScalars
      (baseRingToGlobalSections O)

/-- On objects, `moduleDerivedGlobalSectionsOverBase` is derived global sections followed by
derived restriction of scalars along `A ⟶ Γ(C, O)`. -/
theorem moduleDerivedGlobalSectionsOverBase_obj
    [IsGrothendieckAbelian (ModuleCat.{w} (ofCommRingSheaf J (commRing O)))]
    (F : ModuleDerived.{w} (ofCommRingSheaf J (commRing O))) :
    (moduleDerivedGlobalSectionsOverBase O).obj F =
      (_root_.CategoryTheory.ModuleCat.derivedRestrictionOfScalars
        (baseRingToGlobalSections O)).obj
        ((moduleDerivedGlobalSections
          (ofCommRingSheaf J (commRing O))).obj F) := sorry

end RingedSite.Hom

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
    (baseRingSection O a).val U = baseRingHom O U a := sorry

end SheafOfModules.CommAlg

namespace SheafOfModules.RingedSite.IdealSheaf

open SheafOfModules.RingedSite.ExtendedCech

variable {A : Type w} [CommRing A]
variable {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} A) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable (O : Sheaf J (CommAlgCat.{w} A))

/-- The ideal sheaf `I O` generated by the image of a finitely generated ideal `I ⊆ A`. -/
noncomputable def ofBaseIdeal (I : Ideal A) (hI : I.FG) :
    Subobject (unitModule J (commRing O)) :=
  let G := Ideal.FiniteGeneratingFamily.ofFG I hI
  generatedIdeal (fun i : G.Index ↦
    SheafOfModules.CommAlg.baseRingSection O (G.generator i))

/-- The ideal sheaf `ofBaseIdeal O I hI` is generated by the canonical global sections attached
to the selected finite generating family of `I`. -/
theorem ofBaseIdeal_def (I : Ideal A) (hI : I.FG) :
    ofBaseIdeal O I hI =
      let G := Ideal.FiniteGeneratingFamily.ofFG I hI
      generatedIdeal (fun i : G.Index ↦
        SheafOfModules.CommAlg.baseRingSection O (G.generator i)) := sorry

end SheafOfModules.RingedSite.IdealSheaf
