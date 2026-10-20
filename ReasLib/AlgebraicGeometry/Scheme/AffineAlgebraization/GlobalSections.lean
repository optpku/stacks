module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Support
public import ReasLib.CategoryTheory.Functor.SectionsTerminal
public import ReasLib.Topology.Sheaves.Glue
public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.NeighborhoodComparison

/-!
# Global-section comparison for affine algebraization

This file compares the neighborhood-colimit presentation of ideal-power quotient sections with
their global sections and constructs the resulting map to the infinitesimal inverse limit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The two-open cover used to extend a quotient section: its given neighborhood and the
complement of the ideal support. -/
def supportExtensionCover (S : AffineAlgebraizationSetup A) (V : OpenNeighborhoods S) :
    Bool → Opens S.U
  | false => V.1
  | true => (idealOnOpen S).openComplement

/-- The neighborhood and the complement of the ideal support cover the whole open `S.U`. -/
theorem supportExtensionCover_covers (S : AffineAlgebraizationSetup A)
    (V : OpenNeighborhoods S) :
    (⊤ : Opens S.U) ≤ ⨆ b, supportExtensionCover S V b := sorry

/-- Every ideal-power quotient is supported on the support of the restricted ideal. -/
theorem powerQuotientStage_support_subset (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (n : ℕ) :
    SheafOfModules.support
        (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
          (idealOnOpen S).toSubobject M n) ⊆
      (idealOnOpen S).support := sorry

/-- Local data for extending a quotient section: the given section on its neighborhood and zero
off the ideal support. -/
def supportExtensionFamily (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (n : ℕ) (V : OpenNeighborhoods S)
    (s : (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
      (idealOnOpen S).toSubobject M n).val.obj (op V.1)) :
    ∀ b : Bool,
      (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
        (idealOnOpen S).toSubobject M n).val.obj (op (supportExtensionCover S V b))
  | false => s
  | true => 0

/-- The local data for a supported quotient section agree on the overlap. -/
theorem supportExtensionFamily_compatible (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (n : ℕ) (V : OpenNeighborhoods S)
    (s : (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
      (idealOnOpen S).toSubobject M n).val.obj (op V.1)) :
    TopCat.Presheaf.IsCompatible
      ((SheafOfModules.toSheaf S.U.toScheme.ringCatSheaf).obj
        (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
          (idealOnOpen S).toSubobject M n)).obj
      (supportExtensionCover S V) (supportExtensionFamily S M n V s) := sorry

/-- A quotient section on a neighborhood, extended by zero to the whole open `S.U`. -/
noncomputable def supportExtensionTopSection (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (n : ℕ) (V : OpenNeighborhoods S)
    (s : (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
      (idealOnOpen S).toSubobject M n).val.obj (op V.1)) :
    (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
      (idealOnOpen S).toSubobject M n).val.obj (op (⊤ : Opens S.U)) :=
  TopCat.Sheaf.glueOfCompatibleFamily
    ((SheafOfModules.toSheaf S.U.toScheme.ringCatSheaf).obj
      (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
        (idealOnOpen S).toSubobject M n))
    (supportExtensionCover S V) ⊤ (fun _ ↦ homOfLE le_top)
    (supportExtensionCover_covers S V) (supportExtensionFamily S M n V s)
    (supportExtensionFamily_compatible S M n V s)

/-- Extension by zero sends a quotient section on a neighborhood to a global section. -/
noncomputable def supportedSectionExtension (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (n : ℕ) (V : OpenNeighborhoods S) :
    ((SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
      (idealOnOpen S).toSubobject M n).val.obj (op V.1) : Type u) ⟶
      (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
        (idealOnOpen S).toSubobject M n).sections :=
  ↾fun s ↦
    (Functor.sectionsEquivTerminal
      ((SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
        (idealOnOpen S).toSubobject M n).val.presheaf ⋙
          CategoryTheory.forget AddCommGrpCat) ⊤ isTerminalTop).symm
      (supportExtensionTopSection S M n V s)

/-- Restricting a supported extension to its original neighborhood recovers the section. -/
theorem supportedSectionExtension_eval (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (n : ℕ) (V : OpenNeighborhoods S)
    (s : (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
      (idealOnOpen S).toSubobject M n).val.obj (op V.1)) :
    (supportedSectionExtension S M n V s).val (op V.1) = s := sorry

/-- Supported extension is compatible with restriction between neighborhoods. -/
theorem supportedSectionExtension_naturality (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (n : ℕ) {V W : (OpenNeighborhoods S)ᵒᵖ}
    (f : V ⟶ W) :
    (neighborhoodQuotientSectionsDiagram S M n).map f ≫
        supportedSectionExtension S M n W.unop =
      supportedSectionExtension S M n V.unop := sorry

/-- Global quotient sections form a cocone over quotient sections on neighborhoods. -/
noncomputable def neighborhoodQuotientSectionsCocone (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (n : ℕ) :
    Cocone (neighborhoodQuotientSectionsDiagram S M n) where
  pt :=
    (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
      (idealOnOpen S).toSubobject M n).sections
  ι :=
    { app := fun V ↦ supportedSectionExtension S M n V.unop
      naturality := fun _ _ f ↦ supportedSectionExtension_naturality S M n f }

/-- The canonical map from the colimit of quotient sections on neighborhoods to global quotient
sections. -/
noncomputable def neighborhoodQuotientSectionsToSections
    (S : AffineAlgebraizationSetup A) (M : S.U.toScheme.Modules) (n : ℕ) :
    colimit (neighborhoodQuotientSectionsDiagram S M n) ⟶
      (SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule.stage.{u, u, u}
        (idealOnOpen S).toSubobject M n).sections :=
  colimit.desc (neighborhoodQuotientSectionsDiagram S M n)
    (neighborhoodQuotientSectionsCocone S M n)

/-- The colimit-to-global-section map agrees with supported extension on each neighborhood. -/
theorem neighborhoodQuotientSectionsToSections_fac
    (S : AffineAlgebraizationSetup A) (M : S.U.toScheme.Modules) (n : ℕ)
    (V : (OpenNeighborhoods S)ᵒᵖ) :
    colimit.ι (neighborhoodQuotientSectionsDiagram S M n) V ≫
        neighborhoodQuotientSectionsToSections S M n =
      supportedSectionExtension S M n V.unop := sorry

/-- At a positive stage, the neighborhood quotient colimit maps to the corresponding global
quotient sections. -/
noncomputable def positiveNeighborhoodToPositiveSectionsApp
    (S : AffineAlgebraizationSetup A) (M : S.U.toScheme.Modules) (n : ℕ) :
    (positiveNeighborhoodSectionsSystem S M).obj (op n) ⟶
      (Scheme.CoherentCompletion.positiveSectionsSystem (idealOnOpen S) M).obj (op n) :=
  eqToHom (positiveNeighborhoodSectionsSystem_obj S M n) ≫
    neighborhoodQuotientSectionsToSections S M (n + 1) ≫
      eqToHom (Scheme.CoherentCompletion.positiveSectionsSystem_obj
        (idealOnOpen S) M n).symm

/-- The stagewise neighborhood-to-global maps commute with ideal-power transitions. -/
theorem positiveNeighborhoodToPositiveSections_naturality
    (S : AffineAlgebraizationSetup A) (M : S.U.toScheme.Modules) (n : ℕ) :
    (positiveNeighborhoodSectionsSystem S M).map
          (homOfLE (Nat.le_add_right n 1)).op ≫
        positiveNeighborhoodToPositiveSectionsApp S M n =
      positiveNeighborhoodToPositiveSectionsApp S M (n + 1) ≫
        (Scheme.CoherentCompletion.positiveSectionsSystem
          (idealOnOpen S) M).map (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The canonical natural transformation from neighborhood-colimit quotient sections to global
quotient sections. -/
noncomputable def positiveNeighborhoodToPositiveSections
    (S : AffineAlgebraizationSetup A) (M : S.U.toScheme.Modules) :
    positiveNeighborhoodSectionsSystem S M ⟶
      Scheme.CoherentCompletion.positiveSectionsSystem (idealOnOpen S) M :=
  NatTrans.ofOpSequence (positiveNeighborhoodToPositiveSectionsApp S M)
    (positiveNeighborhoodToPositiveSections_naturality S M)

/-- The component of the neighborhood-to-global natural transformation is supported extension. -/
theorem positiveNeighborhoodToPositiveSections_app
    (S : AffineAlgebraizationSetup A) (M : S.U.toScheme.Modules) (n : ℕ) :
    (positiveNeighborhoodToPositiveSections S M).app (op n) =
      positiveNeighborhoodToPositiveSectionsApp S M n := sorry

/-- Supported ideal-power quotients identify the neighborhood-colimit and global-section inverse
systems. -/
theorem positiveNeighborhoodToPositiveSections_isIso
    (S : AffineAlgebraizationSetup A) (M : S.U.toScheme.Modules) :
    IsIso (positiveNeighborhoodToPositiveSections S M) := sorry

/-- The limiting cone obtained by applying supported extension to the canonical neighborhood
limit cone. -/
noncomputable def positiveSectionsLimitCone (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) :
    Cone (Scheme.CoherentCompletion.positiveSectionsSystem (idealOnOpen S) M) where
  pt := limit (positiveNeighborhoodSectionsSystem S M)
  π := (limit.cone (positiveNeighborhoodSectionsSystem S M)).π ≫
    positiveNeighborhoodToPositiveSections S M

/-- The map on inverse limits induced by supported extension at every ideal-power stage. -/
noncomputable def positiveSectionsLimitMap (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) :
    limit (positiveNeighborhoodSectionsSystem S M) ⟶
      limit (Scheme.CoherentCompletion.positiveSectionsSystem (idealOnOpen S) M) :=
  limit.lift (Scheme.CoherentCompletion.positiveSectionsSystem (idealOnOpen S) M)
    (positiveSectionsLimitCone S M)

/-- Every projection of the induced limit map is the corresponding supported-extension map. -/
theorem positiveSectionsLimitMap_fac (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (n : ℕ) :
    positiveSectionsLimitMap S M ≫
        limit.π (Scheme.CoherentCompletion.positiveSectionsSystem
          (idealOnOpen S) M) (op n) =
      limit.π (positiveNeighborhoodSectionsSystem S M) (op n) ≫
        positiveNeighborhoodToPositiveSectionsApp S M n := sorry

/-- The canonical map from sections on neighborhoods of the closed fiber to the inverse limit of
global sections of the positive ideal-power quotients. -/
noncomputable def globalNeighborhoodComparison (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) :
    colimit (neighborhoodSectionsDiagram S M) ⟶
      limit (Scheme.CoherentCompletion.positiveSectionsSystem (idealOnOpen S) M) :=
  neighborhoodComparison S M ≫ positiveSectionsLimitMap S M

/-- Every projection of the global-section comparison is quotient projection on neighborhoods
followed by supported extension. -/
theorem globalNeighborhoodComparison_fac (S : AffineAlgebraizationSetup A)
    (M : S.U.toScheme.Modules) (n : ℕ) :
    globalNeighborhoodComparison S M ≫
        limit.π (Scheme.CoherentCompletion.positiveSectionsSystem
          (idealOnOpen S) M) (op n) =
      neighborhoodSectionsProjection S M n ≫
        positiveNeighborhoodToPositiveSectionsApp S M n := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
