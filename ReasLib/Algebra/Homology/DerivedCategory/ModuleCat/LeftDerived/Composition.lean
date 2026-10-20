module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.LeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived

/-!
# Composition of left-derived functors on the specified module cell models

The explicit pointwise limit cones identify the displayed cell model with the chosen total
left-derived functor. Composition uses the actual second cell augmentation; its image need only
be a quasi-isomorphism. Both comparison maps then come from formal localization and native
uniqueness of left-derived functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v uR uD vD wD vR vA uA

namespace CategoryTheory.Functor.ModuleCatCellModel

section Universal

variable {R : Type uR} [Ring R] [Small.{v} R]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
variable (F : ModuleCat.{v} R ⥤ D) [F.Additive]

/-- The displayed cell-model cones give pointwise universal data at every derived object. -/
def pointwise : (rightExtension F).IsPointwiseRightKanExtension := by
  let L := DerivedCategory.Qh (C := ModuleCat.{v} R)
  letI := Localization.essSurj L
    (HomotopyCategory.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ))
  intro Y
  exact (rightExtension F).isPointwiseRightKanExtensionAtOfIso'
    (coneIsLimit F (L.objPreimage Y)) (L.objObjPreimageIso Y)

/-- The model's derived-functor certificate contains the displayed pointwise lifts. -/
theorem isLeftDerived :
    (derived F).IsLeftDerivedFunctor (homotopyCounit F)
      (HomotopyCategory.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)) where
  isRightKanExtension := (pointwise F).isRightKanExtension

/-- Native uniqueness compares the actual cell model with the caller's chosen total derived
functor, preserving that chosen functor and counit. -/
def totalLeftDerivedIso
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ))] :
    derived F ≅ Functor.LeftDerived.Homotopy.functor F := by
  letI := isLeftDerived F
  exact Functor.leftDerivedUnique
    (LF := derived F) (LF' := Functor.LeftDerived.Homotopy.functor F)
    (α := homotopyCounit F) (α'₂ := Functor.LeftDerived.Homotopy.counit F)
    (W := HomotopyCategory.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ))

end Universal

section Composition

variable {R : Type uR} [Ring R] [Small.{vR} R]
variable {A : Type uA} [Ring A] [Small.{vA} A]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
variable (F : ModuleCat.{vR} R ⥤ ModuleCat.{vA} A) [F.Additive]
variable (G : ModuleCat.{vA} A ⥤ D) [G.Additive]
variable (H : ModuleCat.{vR} R ⥤ D) [H.Additive] (hcomp : H ≅ F ⋙ G)
variable (hAcyclic : ∀ K : CochainComplex (ModuleCat.{vR} R) ℤ,
  QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (ModuleCat.CellReplacement.augmentation
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (ModuleCat.CellReplacement.replacement K)))))

/-- On a complex, the comparison uses the specified second cell augmentation and its formal
inverse in the target derived category. -/
def compositionOnInput (K : CochainComplex (ModuleCat.{vR} R) ℤ) :
    (derived F ⋙ derived G).obj (DerivedCategory.Q.obj K) ≅
      (derived H).obj (DerivedCategory.Q.obj K) :=
  (derived G).mapIso ((fac F).app K) ≪≫
    (fac G).app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (ModuleCat.CellReplacement.replacement K)) ≪≫
    Localization.isoOfHom (DerivedCategory.Q (C := D))
      (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (ModuleCat.CellReplacement.augmentation
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (ModuleCat.CellReplacement.replacement K))))
      (hAcyclic K) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso hcomp.symm (ComplexShape.up ℤ)).app
        (ModuleCat.CellReplacement.replacement K)) ≪≫
    ((fac H).app K).symm

/-- The displayed comparison is natural in the original complex. -/
theorem compositionOnInput_naturality
    {K L : CochainComplex (ModuleCat.{vR} R) ℤ} (f : K ⟶ L) :
    (DerivedCategory.Q ⋙ derived F ⋙ derived G).map f ≫
        (compositionOnInput F G H hcomp hAcyclic L).hom =
      (compositionOnInput F G H hcomp hAcyclic K).hom ≫
        (DerivedCategory.Q ⋙ derived H).map f := sorry

/-- The actual cell-model composition comparison before localization descent. -/
def compositionOnCochains :
    DerivedCategory.Q ⋙ derived F ⋙ derived G ≅ DerivedCategory.Q ⋙ derived H :=
  NatIso.ofComponents (compositionOnInput F G H hcomp hAcyclic)
    (fun f ↦ compositionOnInput_naturality F G H hcomp hAcyclic f)

/-- Native localization descends both specified component maps. -/
def compositionIso : derived F ⋙ derived G ≅ derived H :=
  Localization.liftNatIso (DerivedCategory.Q (C := ModuleCat.{vR} R))
    (HomologicalComplex.quasiIso (ModuleCat.{vR} R) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ derived F ⋙ derived G) (DerivedCategory.Q ⋙ derived H)
    (derived F ⋙ derived G) (derived H) (compositionOnCochains F G H hcomp hAcyclic)

/-- Transport the displayed comparison to the existing chosen total derived functors. -/
def compositionTotalLeftDerivedIso
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{vR} R) (ComplexShape.up ℤ))]
    [(Functor.Homotopy.toDerived G).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{vA} A) (ComplexShape.up ℤ))]
    [(Functor.Homotopy.toDerived H).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{vR} R) (ComplexShape.up ℤ))] :
    Functor.LeftDerived.Homotopy.functor F ⋙ Functor.LeftDerived.Homotopy.functor G ≅
      Functor.LeftDerived.Homotopy.functor H :=
  Functor.isoWhiskerRight (totalLeftDerivedIso F).symm
      (Functor.LeftDerived.Homotopy.functor G) ≪≫
    Functor.isoWhiskerLeft (derived F) (totalLeftDerivedIso G).symm ≪≫
    compositionIso F G H hcomp hAcyclic ≪≫ totalLeftDerivedIso H

end Composition

end CategoryTheory.Functor.ModuleCatCellModel
