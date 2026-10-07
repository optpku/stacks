module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory

/-!
# Derived base change along Z/ℓ^{n+2} → Z/ℓ^{n+1}

Ring maps, derived extension of scalars, and the mixed-universe
extension-restriction adjunction used to assemble inverse systems of
perfect complexes over `ZMod (ℓ ^ (n + 1))`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits ComplexShape

namespace DerivedCategory.IsPerfect

/-- The canonical reduction `ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (n + 1))`. -/
abbrev zmodPowStepHom (ℓ n : ℕ) : ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (n + 1)) :=
  ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) _

/-- Unfolding of the successor reduction of `ZMod` powers. -/
theorem zmodPowStepHom_eq (ℓ n : ℕ) :
    zmodPowStepHom ℓ n =
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) _ := sorry

/-- Derived extension of scalars along `zmodPowStepHom`, i.e. `- ⊗^L_{ZMod (ℓ^{n+2})} ZMod (ℓ^{n+1})`. -/
noncomputable abbrev derivedBaseChange (ℓ n : ℕ) :
    DerivedCategory (ModuleCat.{u} (ZMod (ℓ ^ (n + 2)))) ⥤
      DerivedCategory (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))) :=
  ModuleCat.derivedExtensionOfScalars (zmodPowStepHom ℓ n)

/-- Unfolding of derived base change as derived extension of scalars along `zmodPowStepHom`. -/
theorem derivedBaseChange_eq (ℓ n : ℕ) :
    derivedBaseChange ℓ n =
      ModuleCat.derivedExtensionOfScalars (zmodPowStepHom ℓ n) := sorry

variable {R S : Type} [CommRing R] [CommRing S]

/-- Derived restriction of scalars along a ring map, as the exact functor `restrictScalars`
on derived categories. -/
noncomputable abbrev derivedRestriction (σ : R →+* S) :
    DerivedCategory (ModuleCat.{u} S) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (ModuleCat.restrictScalars.{u} σ).mapDerivedCategory

/-- Unfolding of mixed-universe derived restriction as `mapDerivedCategory` of `restrictScalars`. -/
theorem derivedRestriction_eq (σ : R →+* S) :
    derivedRestriction σ = (ModuleCat.restrictScalars.{u} σ).mapDerivedCategory := sorry

/-- Derived extension of scalars is a left derived functor of termwise extension on cochain
complexes. -/
instance instIsLeftDerived_derivedExtension (σ : R →+* S) :
    (ModuleCat.derivedExtensionOfScalars σ).IsLeftDerivedFunctor
      (Functor.LeftDerived.Homotopy.cochainCounit (ModuleCat.extendScalars σ))
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (up ℤ)) :=
  Functor.LeftDerived.Homotopy.cochainIsLeftDerived (ModuleCat.extendScalars σ)

/-- Derived restriction of scalars is a right derived functor of termwise restriction on cochain
complexes. -/
instance instIsRightDerived_derivedRestriction (σ : R →+* S) :
    ((ModuleCat.restrictScalars.{u} σ).mapDerivedCategory).IsRightDerivedFunctor
      (ModuleCat.restrictScalars.{u} σ).mapDerivedCategoryFactors.inv
      (HomologicalComplex.quasiIso (ModuleCat.{u} S) (up ℤ)) := sorry

/-- Derived extension followed by derived restriction remains left derived. -/
instance instIsLeftDerived_derivedExtensionRestriction (σ : R →+* S) :
    (ModuleCat.derivedExtensionOfScalars σ ⋙
        (ModuleCat.restrictScalars.{u} σ).mapDerivedCategory).IsLeftDerivedFunctor
      ((Functor.associator
          (DerivedCategory.Q : CochainComplex (ModuleCat.{u} R) ℤ ⥤
            DerivedCategory (ModuleCat.{u} R))
          (ModuleCat.derivedExtensionOfScalars σ)
          (ModuleCat.restrictScalars.{u} σ).mapDerivedCategory).inv ≫
        Functor.whiskerRight
          (Functor.LeftDerived.Homotopy.cochainCounit (ModuleCat.extendScalars σ))
          (ModuleCat.restrictScalars.{u} σ).mapDerivedCategory)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (up ℤ)) := sorry

/-- Derived restriction followed by derived extension remains right derived. -/
instance instIsRightDerived_derivedRestrictionExtension (σ : R →+* S) :
    ((ModuleCat.restrictScalars.{u} σ).mapDerivedCategory ⋙
        ModuleCat.derivedExtensionOfScalars σ).IsRightDerivedFunctor
      (Functor.whiskerRight
          (ModuleCat.restrictScalars.{u} σ).mapDerivedCategoryFactors.inv
          (ModuleCat.derivedExtensionOfScalars σ) ≫
        (Functor.associator
          (DerivedCategory.Q : CochainComplex (ModuleCat.{u} S) ℤ ⥤
            DerivedCategory (ModuleCat.{u} S))
          (ModuleCat.restrictScalars.{u} σ).mapDerivedCategory
          (ModuleCat.derivedExtensionOfScalars σ)).hom)
      (HomologicalComplex.quasiIso (ModuleCat.{u} S) (up ℤ)) := sorry

/-- Derived extension of scalars is left adjoint to mixed-universe derived restriction. -/
noncomputable def derivedExtensionRestrictionAdjunction (σ : R →+* S) :
    ModuleCat.derivedExtensionOfScalars σ ⊣ derivedRestriction σ :=
  Adjunction.derived
    (Adjunction.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj σ) (up ℤ))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (up ℤ))
    (HomologicalComplex.quasiIso (ModuleCat.{u} S) (up ℤ))
    (Functor.LeftDerived.Homotopy.cochainCounit (ModuleCat.extendScalars σ))
    (ModuleCat.restrictScalars.{u} σ).mapDerivedCategoryFactors.inv

/-- Derived restriction of scalars commutes canonically with homology. -/
noncomputable def derivedRestrictionHomologyIso (σ : R →+* S)
    (L : DerivedCategory (ModuleCat.{u} S)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj ((derivedRestriction σ).obj L) ≅
      (ModuleCat.restrictScalars.{u} σ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj L) :=
  let K := DerivedCategory.Q.objPreimage L
  let FK := ((ModuleCat.restrictScalars.{u} σ).mapHomologicalComplex (up ℤ)).obj K
  let eS :
      (DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj L ≅ K.homology i :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).mapIso
      (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) i).app K
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      ((((derivedRestriction σ).mapIso
        (DerivedCategory.Q.objObjPreimageIso L)).symm) ≪≫
        ((ModuleCat.restrictScalars.{u} σ).mapDerivedCategoryFactors.app K)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app FK ≪≫
    (K.sc i).mapHomologyIso (ModuleCat.restrictScalars.{u} σ) ≪≫
      (ModuleCat.restrictScalars.{u} σ).mapIso eS.symm

/-- Homology of the adjunction transpose of a map out of derived extension of scalars. -/
noncomputable def homologyUntranspose (σ : R →+* S)
    {K : DerivedCategory (ModuleCat.{u} R)} {L : DerivedCategory (ModuleCat.{u} S)}
    (α : (ModuleCat.derivedExtensionOfScalars σ).obj K ⟶ L) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K ⟶
      (ModuleCat.restrictScalars.{u} σ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj L) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map
      ((derivedExtensionRestrictionAdjunction σ).homEquiv K L α) ≫
    (derivedRestrictionHomologyIso σ L i).hom

/-- Unfolding of `homologyUntranspose` as homology of the adjunction transpose, followed by
the restriction-homology comparison. -/
theorem homologyUntranspose_eq (σ : R →+* S)
    {K : DerivedCategory (ModuleCat.{u} R)} {L : DerivedCategory (ModuleCat.{u} S)}
    (α : (ModuleCat.derivedExtensionOfScalars σ).obj K ⟶ L) (i : ℤ) :
    homologyUntranspose σ α i =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map
          ((derivedExtensionRestrictionAdjunction σ).homEquiv K L α) ≫
        (derivedRestrictionHomologyIso σ L i).hom := sorry

end DerivedCategory.IsPerfect
