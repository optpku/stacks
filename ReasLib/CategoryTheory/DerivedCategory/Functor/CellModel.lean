module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CellReplacement.Functorial
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Cochain
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-! # Left-derived functors from the specified sheaf-cell replacement

The input functor is evaluated on the existing actual cell replacement. Its quasi-isomorphism
inversion law is explicit. Every terminal-extension map uses the specified augmentation and
native localization; there is no selection of resolutions or universal witnesses.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe w uC vC uD vD wR wD

namespace CategoryTheory.Functor.CellModel

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasDerivedCategory.{wR} (SheafOfModules.{w} R)]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
variable (F : SheafOfModules.{w} R ⥤ D) [F.Additive]

/-- The given functor applied degreewise, before replacing the input. -/
def ordinaryCochain : CochainComplex (SheafOfModules.{w} R) ℤ ⥤ DerivedCategory D :=
  F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/-- The specified sheaf-cell replacement, degreewise functor, and actual localization. -/
def cochain : CochainComplex (SheafOfModules.{w} R) ℤ ⥤ DerivedCategory D :=
  SheafOfModules.CellReplacement.functor (R := R) ⋙ ordinaryCochain F

variable (hF : (HomologicalComplex.quasiIso (SheafOfModules.{w} R)
  (ComplexShape.up ℤ)).IsInvertedBy (cochain F))

/-- The actual localization of the displayed model functor. -/
def derived : DerivedCategory (SheafOfModules.{w} R) ⥤ DerivedCategory D :=
  Localization.lift (cochain F) hF (DerivedCategory.Q (C := SheafOfModules.{w} R))

/-- The native localization comparison keeps all specified cell-model maps. -/
def fac : DerivedCategory.Q ⋙ derived F hF ≅ cochain F :=
  Localization.fac (cochain F) hF (DerivedCategory.Q (C := SheafOfModules.{w} R))

/-- The left-derived counit is degreewise application to the specified augmentation. -/
def counit : DerivedCategory.Q ⋙ derived F hF ⟶ ordinaryCochain F :=
  (fac F hF).hom ≫
    Functor.whiskerRight (SheafOfModules.CellReplacement.augmentationNatTrans (R := R))
      (ordinaryCochain F) ≫ (Functor.leftUnitor (ordinaryCochain F)).hom

/-- Formal localization of the actual cell-model augmentation at the original input. -/
def inputAugmentationIso (A : CochainComplex (SheafOfModules.{w} R) ℤ) :
    DerivedCategory.Q.obj (SheafOfModules.CellReplacement.model A) ≅ DerivedCategory.Q.obj A :=
  Localization.isoOfHom (DerivedCategory.Q (C := SheafOfModules.{w} R))
    (HomologicalComplex.quasiIso (SheafOfModules.{w} R) (ComplexShape.up ℤ))
    (SheafOfModules.CellReplacement.augmentation A)
    (SheafOfModules.CellReplacement.augmentation_quasiIso A)

/-- The universal lift first reverses the actual input augmentation, then evaluates the given
comparison on the displayed model and reverses the native computation isomorphism. -/
def extensionLiftOnInput
    (G : DerivedCategory (SheafOfModules.{w} R) ⥤ DerivedCategory D)
    (β : DerivedCategory.Q ⋙ G ⟶ ordinaryCochain F)
    (A : CochainComplex (SheafOfModules.{w} R) ℤ) :
    G.obj (DerivedCategory.Q.obj A) ⟶ (derived F hF).obj (DerivedCategory.Q.obj A) :=
  G.map (inputAugmentationIso A).inv ≫
    β.app (SheafOfModules.CellReplacement.model A) ≫ ((fac F hF).app A).inv

/-- The lift formula is natural in each original cochain map. -/
theorem extensionLiftOnInput_naturality
    (G : DerivedCategory (SheafOfModules.{w} R) ⥤ DerivedCategory D)
    (β : DerivedCategory.Q ⋙ G ⟶ ordinaryCochain F)
    {A B : CochainComplex (SheafOfModules.{w} R) ℤ} (a : A ⟶ B) :
    (DerivedCategory.Q ⋙ G).map a ≫ extensionLiftOnInput F hF G β B =
      extensionLiftOnInput F hF G β A ≫ (DerivedCategory.Q ⋙ derived F hF).map a := sorry

/-- The actual natural transformation before localization descent. -/
def extensionLiftOnCochains
    (G : DerivedCategory (SheafOfModules.{w} R) ⥤ DerivedCategory D)
    (β : DerivedCategory.Q ⋙ G ⟶ ordinaryCochain F) :
    DerivedCategory.Q ⋙ G ⟶ DerivedCategory.Q ⋙ derived F hF where
  app A := extensionLiftOnInput F hF G β A
  naturality := fun _ _ a ↦ extensionLiftOnInput_naturality F hF G β a

/-- Native localization descends the displayed lift maps. -/
def extensionLift
    (G : DerivedCategory (SheafOfModules.{w} R) ⥤ DerivedCategory D)
    (β : DerivedCategory.Q ⋙ G ⟶ ordinaryCochain F) : G ⟶ derived F hF :=
  Localization.liftNatTrans (DerivedCategory.Q (C := SheafOfModules.{w} R))
    (HomologicalComplex.quasiIso (SheafOfModules.{w} R) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ G) (DerivedCategory.Q ⋙ derived F hF)
    G (derived F hF) (extensionLiftOnCochains F hF G β)

/-- The specified lift satisfies its comparison equation. -/
theorem extensionLift_fac
    (G : DerivedCategory (SheafOfModules.{w} R) ⥤ DerivedCategory D)
    (β : DerivedCategory.Q ⋙ G ⟶ ordinaryCochain F) :
    Functor.whiskerLeft DerivedCategory.Q (extensionLift F hF G β) ≫ counit F hF = β := sorry

/-- A terminal-extension arrow with the actual lift as its morphism. -/
def terminalExtensionLift
    (E : Functor.RightExtension (DerivedCategory.Q (C := SheafOfModules.{w} R))
      (ordinaryCochain F)) : E ⟶ Functor.RightExtension.mk (derived F hF) (counit F hF) :=
  CostructuredArrow.homMk (extensionLift F hF E.left E.hom)
    (extensionLift_fac F hF E.left E.hom)

variable (hAug : ∀ A : CochainComplex (SheafOfModules.{w} R) ℤ,
  IsIso ((ordinaryCochain F).map
    (SheafOfModules.CellReplacement.augmentation (SheafOfModules.CellReplacement.model A))))

include hAug in
/-- Acyclicity at the actual model makes the augmentation comparison uniquely determine the lift. -/
theorem terminalExtensionLift_unique
    (E : Functor.RightExtension (DerivedCategory.Q (C := SheafOfModules.{w} R))
      (ordinaryCochain F))
    (m : E ⟶ Functor.RightExtension.mk (derived F hF) (counit F hF)) :
    m = terminalExtensionLift F hF E := sorry

/-- The universal witness stores actual terminal maps before their Prop laws. -/
def terminalWitness :
    (Functor.RightExtension.mk (derived F hF) (counit F hF)).IsUniversal :=
  IsTerminal.ofUniqueHom (terminalExtensionLift F hF) (terminalExtensionLift_unique F hF hAug)

include hF hAug in
/-- The constructed cochain localization is left derived with its actual counit. -/
theorem isLeftDerived :
    (derived F hF).IsLeftDerivedFunctor (counit F hF)
      (HomologicalComplex.quasiIso (SheafOfModules.{w} R) (ComplexShape.up ℤ)) where
  isRightKanExtension := { nonempty_isUniversal := ⟨terminalWitness F hF hAug⟩ }

include hF hAug in
/-- The cochain existence certificate records this actual terminal witness. -/
theorem hasLeftDerived :
    (ordinaryCochain F).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso (SheafOfModules.{w} R) (ComplexShape.up ℤ)) :=
  by
    letI := isLeftDerived F hF hAug
    exact Functor.HasLeftDerivedFunctor.mk' (LF := derived F hF) (α := counit F hF)

/-- The homotopy counit component uses the same cell augmentation and native quotient map. -/
def homotopyCounitComponent (K : HomotopyCategory (SheafOfModules.{w} R) (ComplexShape.up ℤ)) :
    (derived F hF).obj (DerivedCategory.Qh.obj K) ⟶ (Functor.Homotopy.toDerived F).obj K :=
  (derived F hF).map ((DerivedCategory.quotientCompQhIso (SheafOfModules.{w} R)).hom.app K.as) ≫
    (counit F hF).app K.as ≫ (Functor.Homotopy.cochainIso F).inv.app K.as

/-- The component formula respects chain homotopy. -/
theorem homotopyCounitComponent_naturality
    {A B : HomotopyCategory (SheafOfModules.{w} R) (ComplexShape.up ℤ)} (a : A ⟶ B) :
    (DerivedCategory.Qh ⋙ derived F hF).map a ≫ homotopyCounitComponent F hF B =
      homotopyCounitComponent F hF A ≫ (Functor.Homotopy.toDerived F).map a := sorry

/-- The homotopy counit retains the actual cochain augmentation maps. -/
def homotopyCounit :
    DerivedCategory.Qh ⋙ derived F hF ⟶ Functor.Homotopy.toDerived F where
  app K := homotopyCounitComponent F hF K
  naturality := fun _ _ a ↦ homotopyCounitComponent_naturality F hF a

/-- Any homotopy extension comparison pulls back along the actual quotient comparison. -/
def extensionCochainComparison (G : DerivedCategory (SheafOfModules.{w} R) ⥤ DerivedCategory D)
    (β : DerivedCategory.Qh ⋙ G ⟶ Functor.Homotopy.toDerived F) :
    DerivedCategory.Q ⋙ G ⟶ ordinaryCochain F :=
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso (SheafOfModules.{w} R)) G).inv ≫
    (Functor.associator (HomotopyCategory.quotient (SheafOfModules.{w} R) (ComplexShape.up ℤ))
      DerivedCategory.Qh G).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient (SheafOfModules.{w} R) (ComplexShape.up ℤ)) β ≫
    (Functor.Homotopy.cochainIso F).hom

/-- The actual homotopy universal lift is the specified cochain universal lift. -/
def homotopyExtensionLift (G : DerivedCategory (SheafOfModules.{w} R) ⥤ DerivedCategory D)
    (β : DerivedCategory.Qh ⋙ G ⟶ Functor.Homotopy.toDerived F) : G ⟶ derived F hF :=
  extensionLift F hF G (extensionCochainComparison F G β)

/-- The constructed homotopy lift satisfies its comparison equation. -/
theorem homotopyExtensionLift_fac (G : DerivedCategory (SheafOfModules.{w} R) ⥤ DerivedCategory D)
    (β : DerivedCategory.Qh ⋙ G ⟶ Functor.Homotopy.toDerived F) :
    Functor.whiskerLeft DerivedCategory.Qh (homotopyExtensionLift F hF G β) ≫
      homotopyCounit F hF = β := sorry

/-- The homotopy terminal arrow contains the specified cochain lift. -/
def homotopyTerminalLift
    (E : Functor.RightExtension (DerivedCategory.Qh (C := SheafOfModules.{w} R))
      (Functor.Homotopy.toDerived F)) :
    E ⟶ Functor.RightExtension.mk (derived F hF) (homotopyCounit F hF) :=
  CostructuredArrow.homMk (homotopyExtensionLift F hF E.left E.hom)
    (homotopyExtensionLift_fac F hF E.left E.hom)

include hAug in
/-- Acyclicity at the actual model uniquely determines a homotopy extension arrow. -/
theorem homotopyTerminalLift_unique
    (E : Functor.RightExtension (DerivedCategory.Qh (C := SheafOfModules.{w} R))
      (Functor.Homotopy.toDerived F))
    (m : E ⟶ Functor.RightExtension.mk (derived F hF) (homotopyCounit F hF)) :
    m = homotopyTerminalLift F hF E := sorry

/-- This actual terminal witness supplies the homotopy-derived certificate. -/
def homotopyTerminalWitness :
    (Functor.RightExtension.mk (derived F hF) (homotopyCounit F hF)).IsUniversal :=
  IsTerminal.ofUniqueHom (homotopyTerminalLift F hF) (homotopyTerminalLift_unique F hF hAug)

include hF hAug in
/-- The homotopy-derived property retains the constructed terminal witness. -/
theorem isLeftDerivedHomotopy :
    (derived F hF).IsLeftDerivedFunctor (homotopyCounit F hF)
      (HomotopyCategory.quasiIso (SheafOfModules.{w} R) (ComplexShape.up ℤ)) where
  isRightKanExtension := { nonempty_isUniversal := ⟨homotopyTerminalWitness F hF hAug⟩ }

include hF hAug in
/-- A canonical existence certificate from the actual homotopy extension data. -/
theorem hasLeftDerivedHomotopy :
    (Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{w} R) (ComplexShape.up ℤ)) :=
  by
    letI := isLeftDerivedHomotopy F hF hAug
    exact Functor.HasLeftDerivedFunctor.mk' (LF := derived F hF) (α := homotopyCounit F hF)

/-- Native uniqueness compares the actual producer with any supplied homotopy-derived model. -/
def isoOfHomotopyModel (G : DerivedCategory (SheafOfModules.{w} R) ⥤ DerivedCategory D)
    (β : DerivedCategory.Qh ⋙ G ⟶ Functor.Homotopy.toDerived F)
    [G.IsLeftDerivedFunctor β
      (HomotopyCategory.quasiIso (SheafOfModules.{w} R) (ComplexShape.up ℤ))] :
    derived F hF ≅ G :=
  by
    letI := isLeftDerivedHomotopy F hF hAug
    exact Functor.leftDerivedUnique (LF := derived F hF) (LF' := G)
      (α := homotopyCounit F hF) (α'₂ := β)
      (W := HomotopyCategory.quasiIso (SheafOfModules.{w} R) (ComplexShape.up ℤ))

end CategoryTheory.Functor.CellModel
