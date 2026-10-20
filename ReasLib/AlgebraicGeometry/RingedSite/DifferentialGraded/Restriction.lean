module

public import ReasLib.AlgebraicGeometry.RingedSite.DifferentialGraded.Module.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Continuous
public import ReasLib.CategoryTheory.Functor.Flat
public import ReasLib.CategoryTheory.Sites.Chaotic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction on chaotic commutative ringed sites

A functor `F : C ⥤ D` restricts presheaves on `D` to presheaves on `C`.  For chaotic
topologies this is literally continuous pushforward.  If `F` is representably flat, the same
data form a morphism of ringed-site presentations, so the existing monoidal adjunction transports
differential graded algebras and modules without any caller-supplied functor or comparison map.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe uC vC uD vD w

namespace RingedSite.Chaotic

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- Restriction of a commutative-ring-valued sheaf along a functor between chaotic sites. -/
@[stacks 0GZE "restriction of the structure sheaf"]
def restrictSheaf (F : C ⥤ D)
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w}) :
    Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{w} :=
  (F.sheafPushforwardContinuous CommRingCat.{w}
    (⊥ : GrothendieckTopology C) (⊥ : GrothendieckTopology D)).obj O

/-- Restriction of a sheaf evaluates by precomposition with the opposite functor. -/
@[simp]
theorem restrictSheaf_obj (F : C ⥤ D)
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w}) (U : Cᵒᵖ) :
    (restrictSheaf F O).obj.obj U = O.obj.obj (F.op.obj U) := sorry

/-- Restriction of a sheaf maps a morphism by precomposition with the opposite functor. -/
@[simp]
theorem restrictSheaf_map (F : C ⥤ D)
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w})
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (restrictSheaf F O).obj.map f = O.obj.map (F.op.map f) := sorry

/-- A representably flat functor is a morphism between the corresponding chaotic sites. -/
@[stacks 0GZE "morphism of chaotic sites"]
instance isMorphismOfSites (F : C ⥤ D) [RepresentablyFlat F] :
    IsMorphismOfSites (⊥ : GrothendieckTopology C)
      (⊥ : GrothendieckTopology D) F := sorry

/-- The ringed-site morphism whose direct image is restriction along `F`.  Its structure map is
the canonical identity from the restricted structure sheaf to itself, viewed after forgetting
commutativity. -/
@[stacks 0GZE "restriction of a chaotic commutative ringed site"]
def restrictionHom (F : C ⥤ D) [RepresentablyFlat F]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w}) :
    RingedSite.Hom
      (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology D) O)
      (RingedSite.ofCommRingSheaf (⊥ : GrothendieckTopology C) (restrictSheaf F O)) where
  base := F
  isMorphismOfSites := inferInstance
  structureSheafMap :=
    SheafOfModules.RingedSite.moduleStructureMap
      (JX := (⊥ : GrothendieckTopology C))
      (JY := (⊥ : GrothendieckTopology D))
      (OX := restrictSheaf F O) (OY := O) F (𝟙 (restrictSheaf F O))

/-- The base functor of the chaotic ringed-site restriction is the original functor. -/
@[simp]
theorem restrictionHom_base (F : C ⥤ D) [RepresentablyFlat F]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w}) :
    (restrictionHom F O).base = F := sorry

/-- The structure map of chaotic ringed-site restriction is induced by the identity map of the
restricted commutative structure sheaf. -/
@[simp]
theorem restrictionHom_structureSheafMap (F : C ⥤ D) [RepresentablyFlat F]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w}) :
    (restrictionHom F O).structureSheafMap =
      SheafOfModules.RingedSite.moduleStructureMap
        (JX := (⊥ : GrothendieckTopology C))
        (JY := (⊥ : GrothendieckTopology D))
        (OX := restrictSheaf F O) (OY := O) F (𝟙 (restrictSheaf F O)) := sorry

/- The presheaf-level module restriction underlying `restrictionHom` has a left adjoint under
the standard universe bounds.  Registering this canonical instance keeps all later DGA and DG
module constructions free of local instance pins. -/
namespace restrictionHom

@[stacks 0GZE "module restriction admits extension"]
noncomputable instance pushforwardIsRightAdjoint
    (F : C ⥤ D) [RepresentablyFlat F]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w})
    [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}] :
    (PresheafOfModules.pushforward.{w}
      (restrictionHom F O).structureSheafMap.hom).IsRightAdjoint := sorry

end restrictionHom

/-- Restriction of differential graded algebras along a representably flat functor between
chaotic ringed sites. -/
@[stacks 0GZE "restriction of differential graded algebras"]
noncomputable def restrictDGA (F : C ⥤ D) [RepresentablyFlat F]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w})
    [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}] :
    DGA(O) ⥤
      SheafOfModules.RingedSite.DifferentialGradedAlgebra
        (C := C) (J := (⊥ : GrothendieckTopology C)) (𝒪 := restrictSheaf F O) :=
  SheafOfModules.RingedSite.DifferentialGradedAlgebra.map
    (C := D) (D := C)
    (JC := (⊥ : GrothendieckTopology D))
    (JD := (⊥ : GrothendieckTopology C))
    (OC := O) (OD := restrictSheaf F O)
    (restrictionHom (C := C) (D := D) F O).modulePushforwardComplex.{w}

/-- The coefficient DGA obtained by restriction along a representably flat functor between
chaotic sites. -/
@[stacks 0GZE "restricted differential graded algebra"]
abbrev restrictedDGA (F : C ⥤ D) [RepresentablyFlat F]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w})
    [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}]
    (A : DGA(O)) :
      SheafOfModules.RingedSite.DifferentialGradedAlgebra
        (C := C) (J := (⊥ : GrothendieckTopology C)) (𝒪 := restrictSheaf F O) :=
  (restrictDGA F O).obj A

/-- The underlying complex of a restricted DGA is obtained by degreewise module restriction. -/
@[simp]
theorem restrictDGA_obj_toComplex (F : C ⥤ D) [RepresentablyFlat F]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w})
    [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}] (A : DGA(O)) :
    (restrictedDGA F O A).toComplex =
      (restrictionHom F O).modulePushforwardComplex.{w}.obj A.toComplex := sorry

/-- The DGA pullback functor underlying the coefficient comparison for chaotic restriction. -/
@[stacks 0GZE "pullback of the restricted coefficient DGA"]
noncomputable abbrev restrictedPullbackDGA
    (F : C ⥤ D) [RepresentablyFlat F]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w})
    [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}] :
    SheafOfModules.RingedSite.DifferentialGradedAlgebra
        (C := C) (J := (⊥ : GrothendieckTopology C)) (𝒪 := restrictSheaf F O) ⥤
      DGA(O) :=
  SheafOfModules.RingedSite.DifferentialGradedAlgebra.map
    (C := C) (D := D)
    (JC := (⊥ : GrothendieckTopology C))
    (JD := (⊥ : GrothendieckTopology D))
    (OC := restrictSheaf F O) (OD := O)
    (restrictionHom (C := C) (D := D) F O).modulePullbackComplex.{w}

/-- The source of the chaotic-restriction DGA counit agrees with pullback of the restricted
coefficient DGA. -/
@[stacks 0GZE "source of the restricted coefficient counit"]
theorem dgaCounit_source_eq (F : C ⥤ D) [RepresentablyFlat F]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w})
    [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}] (A : DGA(O)) :
    (restrictedPullbackDGA F O).obj (restrictedDGA F O A) =
      ((SheafOfModules.RingedSite.DifferentialGradedAlgebra.map
          (C := D) (D := C)
          (JC := (⊥ : GrothendieckTopology D))
          (JD := (⊥ : GrothendieckTopology C))
          (OC := O) (OD := restrictSheaf F O)
          (restrictionHom (C := C) (D := D) F O).modulePushforwardComplex.{w}) ⋙
        restrictedPullbackDGA F O).obj A := sorry

/-- The target of the chaotic-restriction DGA counit is the original coefficient DGA. -/
@[stacks 0GZE "target of the restricted coefficient counit"]
theorem dgaCounit_target_eq (F : C ⥤ D) [RepresentablyFlat F]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w})
    [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}] (A : DGA(O)) :
    (𝟭 DGA(O)).obj A = A := sorry

/-- The canonical map from the pullback of a restricted DGA to the original DGA. -/
@[stacks 0GZE "restriction-pullback coefficient comparison"]
noncomputable def dgaCounit (F : C ⥤ D) [RepresentablyFlat F]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w})
    [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}] (A : DGA(O)) :
    (restrictedPullbackDGA F O).obj (restrictedDGA F O A) ⟶ A :=
  eqToHom (dgaCounit_source_eq F O A) ≫
  (SheafOfModules.RingedSite.DifferentialGradedAlgebra.mapAdjunction
    (C := C) (D := D)
    (JC := (⊥ : GrothendieckTopology C))
    (JD := (⊥ : GrothendieckTopology D))
    (OC := restrictSheaf F O) (OD := O)
    (restrictionHom (C := C) (D := D) F O).modulePushforwardComplex.{w}
    (RingedSite.Hom.modulePullbackPushforwardComplexAdjunction.{w}
      (restrictionHom (C := C) (D := D) F O))).counit.app A ≫
    eqToHom (dgaCounit_target_eq F O A)

/-- The category of right DG modules over a coefficient DGA restricted along a
representably flat functor between chaotic sites. -/
@[stacks 0GZE "modules over a restricted differential graded algebra"]
abbrev RestrictedDGModule (F : C ⥤ D) [RepresentablyFlat F]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w})
    [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}] (A : DGA(O)) :=
  SheafOfModules.RingedSite.DifferentialGradedModule
    (C := C) (J := (⊥ : GrothendieckTopology C)) (𝒪 := restrictSheaf F O)
    (restrictedDGA F O A)

/-- Restriction of right DG modules to the restricted DGA. -/
@[stacks 0GZE "restriction of differential graded modules"]
noncomputable def restrictDGModule (F : C ⥤ D) [RepresentablyFlat F]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w})
    [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}] (A : DGA(O)) :
    Mod(A, d) ⥤ RestrictedDGModule F O A :=
  SheafOfModules.RingedSite.DifferentialGradedModule.BaseChange.pushforward
    (C := C) (D := D)
    (JC := (⊥ : GrothendieckTopology C))
    (JD := (⊥ : GrothendieckTopology D))
    (OC := restrictSheaf F O) (OD := O)
    (F := (restrictionHom (C := C) (D := D) F O).modulePullbackComplex.{w})
    (G := (restrictionHom (C := C) (D := D) F O).modulePushforwardComplex.{w})
    (A := restrictedDGA F O A) (B := A)
    (RingedSite.Hom.modulePullbackPushforwardComplexAdjunction.{w}
      (restrictionHom (C := C) (D := D) F O))
    (dgaCounit (C := C) (D := D) F O A)

/-- Extension of right DG modules from the restricted DGA, left adjoint to restriction. -/
@[stacks 0GZE "extension of differential graded modules"]
noncomputable def extendDGModule (F : C ⥤ D) [RepresentablyFlat F]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w})
    [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}] (A : DGA(O)) :
    RestrictedDGModule F O A ⥤ Mod(A, d) :=
  SheafOfModules.RingedSite.DifferentialGradedModule.baseChange
    (C := C) (D := D)
    (JC := (⊥ : GrothendieckTopology C))
    (JD := (⊥ : GrothendieckTopology D))
    (OC := restrictSheaf F O) (OD := O)
    (A := restrictedDGA F O A) (B := A)
    (restrictionHom (C := C) (D := D) F O).modulePullbackComplex.{w}
    (dgaCounit (C := C) (D := D) F O A)

/-- Extension and restriction of DG modules along a chaotic-site functor form the canonical
base-change adjunction. -/
@[stacks 0GZE "DG module extension-restriction adjunction"]
noncomputable def dgModuleAdjunction (F : C ⥤ D) [RepresentablyFlat F]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w})
    [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}] (A : DGA(O)) :
    extendDGModule F O A ⊣ restrictDGModule F O A :=
  SheafOfModules.RingedSite.DifferentialGradedModule.BaseChange.adjunction
    (C := C) (D := D)
    (JC := (⊥ : GrothendieckTopology C))
    (JD := (⊥ : GrothendieckTopology D))
    (OC := restrictSheaf F O) (OD := O)
    (F := (restrictionHom (C := C) (D := D) F O).modulePullbackComplex.{w})
    (G := (restrictionHom (C := C) (D := D) F O).modulePushforwardComplex.{w})
    (A := restrictedDGA F O A) (B := A)
    (RingedSite.Hom.modulePullbackPushforwardComplexAdjunction.{w}
      (restrictionHom (C := C) (D := D) F O))
    (dgaCounit (C := C) (D := D) F O A)

/-- DG module restriction applies degreewise module restriction to the underlying complex. -/
@[simp]
theorem restrictDGModule_obj_toComplex (F : C ⥤ D) [RepresentablyFlat F]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w})
    [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}]
    (A : DGA(O)) (M : Mod(A, d)) :
    ((restrictDGModule F O A).obj M).toComplex =
      (restrictionHom F O).modulePushforwardComplex.{w}.obj M.toComplex := sorry

/-- DG module extension applies degreewise module pullback to the underlying complex. -/
@[simp]
theorem extendDGModule_obj_toComplex (F : C ⥤ D) [RepresentablyFlat F]
    (O : Sheaf (⊥ : GrothendieckTopology D) CommRingCat.{w})
    [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}]
    (A : DGA(O)) (M : RestrictedDGModule F O A) :
    ((extendDGModule F O A).obj M).toComplex =
      (restrictionHom F O).modulePullbackComplex.{w}.obj M.toComplex := sorry

end RingedSite.Chaotic
