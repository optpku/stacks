module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Presentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal

/-!
# The twisted-global-sections counit on `Proj`

This file isolates the categorical counit used by Lemma 27.10.7.  The category of graded
modules and the two functors are explicit parameters until the project has a canonical bundled
implementation; their object formula is pinned degreewise to the concrete twist-section
functors below.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A]
variable {sigma : Type u} [SetLike sigma A] [AddSubgroupClass sigma A]
variable (calA : Nat -> sigma) [GradedRing calA]

namespace ProjTwistedGlobalSections

/-- Global sections of the `n`th chosen twist of a quasi-coherent module on `Proj calA`,
functorially in the module. -/
noncomputable abbrev twistSectionsFunctor (P : ProjTwistPresentation calA) (n : Int) :
    Scheme.QCoh (Proj calA) ⥤
      ModuleCat (RingedSpace.globalSectionsRing (Proj calA).toRingedSpace) :=
  Scheme.QCoh.inclusion (Proj calA) ⋙ tensorRight (P.actualTwist n) ⋙
    RingedSpace.moduleGlobalSectionsFunctor (Proj calA).toRingedSpace

/-- The canonical identification `F(0) ≅ F` induced by the chosen degree-zero twist
identification and the right unitor. -/
noncomputable def tensorTwistZeroIso
    (P : ProjTwistPresentation calA) (F : (Proj calA).Modules) :
    P.tensorTwist F 0 ≅ F :=
  (Iso.refl F ⊗ᵢ P.twistAlgebra.twist_zero) ≪≫
    (Iso.refl F ⊗ᵢ RingedSpace.unitIsoTensorUnit (Proj calA).toRingedSpace) ≪≫ ρ_ F

/-- The defining factorization of `tensorTwistZeroIso` through the degree-zero twist and the
right unitor. -/
theorem tensorTwistZeroIso_def
    (P : ProjTwistPresentation calA) (F : (Proj calA).Modules) :
    tensorTwistZeroIso calA P F =
      (Iso.refl F ⊗ᵢ P.twistAlgebra.twist_zero) ≪≫
        (Iso.refl F ⊗ᵢ RingedSpace.unitIsoTensorUnit (Proj calA).toRingedSpace) ≪≫ ρ_ F := sorry

/-- The degree-zero twist-section functor is naturally isomorphic to ordinary global sections. -/
noncomputable def twistZeroIso (P : ProjTwistPresentation calA) :
    twistSectionsFunctor calA P 0 ≅
      Scheme.QCoh.inclusion (Proj calA) ⋙
        RingedSpace.moduleGlobalSectionsFunctor (Proj calA).toRingedSpace where
  hom :=
    { app := fun F ↦
        (RingedSpace.moduleGlobalSectionsFunctor (Proj calA).toRingedSpace).map
          (tensorTwistZeroIso calA P ((Scheme.QCoh.inclusion (Proj calA)).obj F)).hom
      naturality := sorry }
  inv :=
    { app := fun F ↦
        (RingedSpace.moduleGlobalSectionsFunctor (Proj calA).toRingedSpace).map
          (tensorTwistZeroIso calA P ((Scheme.QCoh.inclusion (Proj calA)).obj F)).inv
      naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The component of `twistZeroIso` is the global-sections map induced by
`tensorTwistZeroIso`. -/
theorem twistZeroIso_hom_app (P : ProjTwistPresentation calA)
    (F : Scheme.QCoh (Proj calA)) :
    (twistZeroIso calA P).hom.app F =
      (RingedSpace.moduleGlobalSectionsFunctor (Proj calA).toRingedSpace).map
        (tensorTwistZeroIso calA P ((Scheme.QCoh.inclusion (Proj calA)).obj F)).hom := sorry

section Counit

variable {C D E : Type v} [Category.{u} C] [Category.{u} D] [Category.{u} E]

/-- The canonical counit associated to a graded associated-sheaf/global-sections adjunction. -/
def counit (associated : C ⥤ D) (twistedSections : D ⥤ C)
    (adjunction : associated ⊣ twistedSections) :
    twistedSections ⋙ associated ⟶ 𝟭 D :=
  adjunction.counit

/-- The component of `counit` is the counit component of the supplied adjunction. -/
theorem counit_app (associated : C ⥤ D) (twistedSections : D ⥤ C)
    (adjunction : associated ⊣ twistedSections) (F : D) :
    (counit associated twistedSections adjunction).app F = adjunction.counit.app F := sorry

/-- The degree-zero section map obtained by applying a degree-zero functor to the adjunction
unit and then identifying the degree-zero part of twisted global sections. -/
def degreeZeroSection (associated : C ⥤ D) (twistedSections : D ⥤ C)
    (degreeZero : C ⥤ E) (globalSections : D ⥤ E)
    (adjunction : associated ⊣ twistedSections)
    (degreeZeroIso : twistedSections ⋙ degreeZero ≅ globalSections) :
    degreeZero ⟶ associated ⋙ globalSections where
  app M := degreeZero.map (adjunction.unit.app M) ≫ degreeZeroIso.hom.app (associated.obj M)
  naturality := sorry

/-- Evaluation of `degreeZeroSection` is application of the degree-zero functor to the unit,
followed by the chosen concrete degree-zero identification. -/
theorem degreeZeroSection_app (associated : C ⥤ D) (twistedSections : D ⥤ C)
    (degreeZero : C ⥤ E) (globalSections : D ⥤ E)
    (adjunction : associated ⊣ twistedSections)
    (degreeZeroIso : twistedSections ⋙ degreeZero ≅ globalSections) (M : C) :
    (degreeZeroSection associated twistedSections degreeZero globalSections adjunction
        degreeZeroIso).app M =
      degreeZero.map (adjunction.unit.app M) ≫
        degreeZeroIso.hom.app (associated.obj M) := sorry

/-- The degree-zero component of the counit is the identity after the canonical identification
of the degree-zero part of twisted global sections. -/
theorem degreeZeroSection_comp_counit (associated : C ⥤ D) (twistedSections : D ⥤ C)
    (degreeZero : C ⥤ E) (globalSections : D ⥤ E)
    (adjunction : associated ⊣ twistedSections)
    (degreeZeroIso : twistedSections ⋙ degreeZero ≅ globalSections) (F : D) :
    (degreeZeroSection associated twistedSections degreeZero globalSections adjunction
          degreeZeroIso).app (twistedSections.obj F) ≫
        globalSections.map ((counit associated twistedSections adjunction).app F) =
      degreeZeroIso.hom.app F := sorry

end Counit

section Proj

variable {C : Type (u + 1)} [Category.{u} C]

/-- For the functor `F ↦ ⨁ n : Int, Γ(Proj calA, F(n))`, the counit from the associated sheaf
back to `F` induces in degree zero the canonical map obtained from `F(0) ≅ F`.

The abstract category `C`, its degree functors, and the adjunction are the narrow interface for
the presently unavailable bundled category of graded `A`-modules and functorial Proj associated
sheaf.  The family `pieceIso` fixes every homogeneous piece to the source formula, so the
comparison map itself is not an input. -/
theorem counit_degreeZero (P : ProjTwistPresentation calA)
    (associated : C ⥤ Scheme.QCoh (Proj calA))
    (twistedSections : Scheme.QCoh (Proj calA) ⥤ C)
    (piece : Int -> C ⥤
      ModuleCat (RingedSpace.globalSectionsRing (Proj calA).toRingedSpace))
    (pieceIso : forall n : Int,
      twistedSections ⋙ piece n ≅ twistSectionsFunctor calA P n)
    (adjunction : associated ⊣ twistedSections) (F : Scheme.QCoh (Proj calA)) :
    (degreeZeroSection associated twistedSections (piece 0)
          (Scheme.QCoh.inclusion (Proj calA) ⋙
            RingedSpace.moduleGlobalSectionsFunctor (Proj calA).toRingedSpace)
          adjunction (pieceIso 0 ≪≫ twistZeroIso calA P)).app (twistedSections.obj F) ≫
        (Scheme.QCoh.inclusion (Proj calA) ⋙
            RingedSpace.moduleGlobalSectionsFunctor (Proj calA).toRingedSpace).map
          ((counit associated twistedSections adjunction).app F) =
      (pieceIso 0).hom.app F ≫ (twistZeroIso calA P).hom.app F := sorry

end Proj

end ProjTwistedGlobalSections

end AlgebraicGeometry
