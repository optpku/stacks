module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Affine
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.AffineBase
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.OpenImmersion

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.Limits
open AlgebraicGeometry
open LocalCohomology
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IdealComplement

variable {A : Type u} [CommRing A]

/-- Cohomology on the complement of the zero locus of an ideal, with scalars restricted to the
ambient affine scheme. -/
noncomputable abbrev cohomologyFunctor (I : Ideal A) (p : ℕ) :
    (idealComplementOpens I).toScheme.Modules ⥤ ModuleCat A :=
  Scheme.Hom.cohomologyFunctor (idealComplementOpens I).ι p

/-- The degree-`p` cohomology module of a module on an affine ideal complement. -/
noncomputable abbrev cohomology (I : Ideal A)
    (F : (idealComplementOpens I).toScheme.Modules) (p : ℕ) : ModuleCat A :=
  (cohomologyFunctor I p).obj F

/-- Degree-zero cohomology on an affine ideal complement is the corresponding module of global
sections with restricted scalars. -/
theorem cohomologyFunctorZero_isomorphic (I : Ideal A)
    (F : (idealComplementOpens I).toScheme.Modules) :
    IsIsomorphic (cohomology I F 0)
      ((ModuleCat.restrictScalars
          (Scheme.Hom.globalSectionsMap (idealComplementOpens I).ι)).obj
        ((RingedSpace.moduleGlobalSectionsFunctor
          (idealComplementOpens I).toScheme.toRingedSpace).obj F)) := sorry

end AlgebraicGeometry.Scheme.Modules.IdealComplement

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A : Type u} [CommRing A]

/-- The degree-`n` local cohomology module supported on the zero locus of an ideal. -/
noncomputable abbrev supportedCohomology (I : Ideal A)
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (M : ModuleCat A) (n : ℤ) : ModuleCat A :=
  (DerivedCategory.homologyFunctor (ModuleCat A) n).obj
    (RΓ.obj (ModuleCat.single0 M)).obj

/-- Every local cohomology module computed in the ideal-power-torsion subcategory is
power-torsion for the supporting ideal. -/
theorem supportedCohomology_isIdealPowerTorsion (I : Ideal A)
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (M : ModuleCat A) (n : ℤ) :
    Module.IsIdealPowerTorsion I (supportedCohomology I RΓ M n) := sorry

/-- The supported local cohomology module is independent up to isomorphism of the chosen
right-adjoint presentation. -/
theorem supportedCohomology_isomorphic (I : Ideal A)
    (RΓ RΓ' : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ)
    (hRΓ' : IdealPowerTorsion.inclusion I ⊣ RΓ')
    (M : ModuleCat A) (n : ℤ) :
    IsIsomorphic (supportedCohomology I RΓ M n)
      (supportedCohomology I RΓ' M n) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology

namespace AlgebraicGeometry.Scheme.Modules.IdealComplement

variable {A : Type u} [CommRing A]

/-- A quasicoherent module on an affine ideal complement is the restriction of an affine tilde
module. -/
theorem exists_tildeRestriction (I : Ideal A) (hI : I.FG)
    (F : (idealComplementOpens I).toScheme.Modules) [F.IsQuasicoherent] :
    ∃ M : ModuleCat A,
      IsIsomorphic ((AlgebraicGeometry.tilde M).restrict (idealComplementOpens I).ι) F := sorry

/-- An affine tilde presentation gives the five-term exact sequence relating supported and
complement cohomology. -/
theorem existsExactSequence (I : Ideal A) (hI : I.FG)
    (F : (idealComplementOpens I).toScheme.Modules) [F.IsQuasicoherent]
    (M : ModuleCat A)
    (e : (AlgebraicGeometry.tilde M).restrict (idealComplementOpens I).ι ≅ F)
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ) :
    ∃ a : supportedCohomology I RΓ M 0 ⟶ M,
      ∃ b : M ⟶ cohomology I F 0,
        ∃ c : cohomology I F 0 ⟶ supportedCohomology I RΓ M 1,
          Mono a ∧ (ComposableArrows.mk₃ a b c).Exact ∧ Epi c := sorry

/-- In positive degree, cohomology on an affine ideal complement is the next supported local
cohomology module of any affine tilde presentation. -/
theorem higherCohomology_isomorphic (I : Ideal A) (hI : I.FG)
    (F : (idealComplementOpens I).toScheme.Modules) [F.IsQuasicoherent]
    (M : ModuleCat A)
    (e : (AlgebraicGeometry.tilde M).restrict (idealComplementOpens I).ι ≅ F)
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ)
    (p : ℕ) (hp : 0 < p) :
    IsIsomorphic (cohomology I F p)
      (supportedCohomology I RΓ M ((p + 1 : ℕ) : ℤ)) := sorry

/-- The degree-zero cohomology module gives a tilde presentation of a quasicoherent module on an
affine ideal complement. -/
theorem cohomologyZero_tildeRestriction_isomorphic (I : Ideal A) (hI : I.FG)
    (F : (idealComplementOpens I).toScheme.Modules) [F.IsQuasicoherent] :
    IsIsomorphic
      ((AlgebraicGeometry.tilde (cohomology I F 0 : ModuleCat A)).restrict
        (idealComplementOpens I).ι) F := sorry

/-- Degree-zero supported local cohomology vanishes for the canonical degree-zero presentation. -/
theorem cohomologyZero_supportedH0_isZero (I : Ideal A) (hI : I.FG)
    (F : (idealComplementOpens I).toScheme.Modules) [F.IsQuasicoherent]
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ) :
    IsZero (supportedCohomology I RΓ (cohomology I F 0) 0) := sorry

/-- Degree-one supported local cohomology vanishes for the canonical degree-zero presentation. -/
theorem cohomologyZero_supportedH1_isZero (I : Ideal A) (hI : I.FG)
    (F : (idealComplementOpens I).toScheme.Modules) [F.IsQuasicoherent]
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ) :
    IsZero (supportedCohomology I RΓ (cohomology I F 0) 1) := sorry

/-- A coherent module on an affine ideal complement over a Noetherian ring is the restriction
of the tilde module of a finite module. -/
theorem existsFiniteExtension [IsNoetherianRing A] (I : Ideal A)
    (F : (idealComplementOpens I).toScheme.Modules) [F.IsCoherent] :
    ∃ M : ModuleCat A, Module.Finite A M ∧
      IsIsomorphic ((AlgebraicGeometry.tilde M).restrict (idealComplementOpens I).ι) F := sorry

/-- A finite tilde extension of a coherent module on an affine ideal complement over a
Noetherian ring gives the five-term exact sequence relating supported and complement
cohomology. -/
theorem existsExactSequence_of_finiteExtension [IsNoetherianRing A] (I : Ideal A)
    (F : (idealComplementOpens I).toScheme.Modules) [F.IsCoherent]
    (M : ModuleCat A) [Module.Finite A M]
    (e : (AlgebraicGeometry.tilde M).restrict (idealComplementOpens I).ι ≅ F)
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ) :
    ∃ a : supportedCohomology I RΓ M 0 ⟶ M,
      ∃ b : M ⟶ cohomology I F 0,
        ∃ c : cohomology I F 0 ⟶ supportedCohomology I RΓ M 1,
          Mono a ∧ (ComposableArrows.mk₃ a b c).Exact ∧ Epi c := sorry

/-- Positive-degree cohomology of a coherent module on an affine ideal complement over a
Noetherian ring is the next supported local cohomology module of any finite tilde extension. -/
theorem higherCohomology_isomorphic_of_finiteExtension [IsNoetherianRing A] (I : Ideal A)
    (F : (idealComplementOpens I).toScheme.Modules) [F.IsCoherent]
    (M : ModuleCat A) [Module.Finite A M]
    (e : (AlgebraicGeometry.tilde M).restrict (idealComplementOpens I).ι ≅ F)
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ)
    (p : ℕ) (hp : 0 < p) :
    IsIsomorphic (cohomology I F p)
      (supportedCohomology I RΓ M ((p + 1 : ℕ) : ℤ)) := sorry

/-- The higher direct image of a coherent module from an affine ideal complement over a
Noetherian ring is coherent exactly when its complement cohomology module is finite. -/
theorem higherDirectImage_isCoherent_iff_cohomology_finite [IsNoetherianRing A] (I : Ideal A)
    (F : (idealComplementOpens I).toScheme.Modules) [F.IsCoherent] (p : ℕ) :
    (RingedSpace.Hom.higherDirectImageModule
      (idealComplementOpens I).ι.toShHom F p).IsCoherent ↔
      Module.Finite A (cohomology I F p) := sorry

/-- For a finite tilde extension of a coherent module on an affine ideal complement over a
Noetherian ring, finiteness of complement cohomology is equivalent to finiteness of the next
supported local cohomology module, including in degree zero. -/
theorem cohomology_finite_iff_supportedCohomology_finite [IsNoetherianRing A] (I : Ideal A)
    (F : (idealComplementOpens I).toScheme.Modules) [F.IsCoherent]
    (M : ModuleCat A) [Module.Finite A M]
    (e : (AlgebraicGeometry.tilde M).restrict (idealComplementOpens I).ι ≅ F)
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ) (p : ℕ) :
    Module.Finite A (cohomology I F p) ↔
      Module.Finite A (supportedCohomology I RΓ M ((p + 1 : ℕ) : ℤ)) := sorry

/-- Finite degree-zero cohomology gives a canonical finite tilde extension of a coherent
module on an affine ideal complement over a Noetherian ring. -/
theorem cohomologyZero_tildeRestriction_isomorphic_of_finite [IsNoetherianRing A] (I : Ideal A)
    (F : (idealComplementOpens I).toScheme.Modules) [F.IsCoherent]
    [Module.Finite A (cohomology I F 0)] :
    IsIsomorphic
      ((AlgebraicGeometry.tilde (cohomology I F 0 : ModuleCat A)).restrict
        (idealComplementOpens I).ι) F := sorry

/-- The canonical finite degree-zero extension of a coherent module on an affine ideal
complement over a Noetherian ring has vanishing degree-zero supported local cohomology. -/
theorem cohomologyZero_supportedH0_isZero_of_finite [IsNoetherianRing A] (I : Ideal A)
    (F : (idealComplementOpens I).toScheme.Modules) [F.IsCoherent]
    [Module.Finite A (cohomology I F 0)]
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ) :
    IsZero (supportedCohomology I RΓ (cohomology I F 0) 0) := sorry

/-- The canonical finite degree-zero extension of a coherent module on an affine ideal
complement over a Noetherian ring has vanishing degree-one supported local cohomology. -/
theorem cohomologyZero_supportedH1_isZero_of_finite [IsNoetherianRing A] (I : Ideal A)
    (F : (idealComplementOpens I).toScheme.Modules) [F.IsCoherent]
    [Module.Finite A (cohomology I F 0)]
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ) :
    IsZero (supportedCohomology I RΓ (cohomology I F 0) 1) := sorry

end AlgebraicGeometry.Scheme.Modules.IdealComplement
