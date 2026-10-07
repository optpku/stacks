module

public import ReasLib.Algebra.Homology.CochainComplex.Nat.Derived
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Coefficients
public import ReasLib.RingTheory.Kaehler.DeRham.Map

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/-- The ringed space on `Spec A` with coefficient sheaf pulled back from `Spec R` along the
morphism induced by `f : R ⟶ A`. -/
abbrev affineCoefficientSpace {R A : CommRingCat.{u}} (f : R ⟶ A) : RingedSpace.{u} :=
  ModuleCech.relativeSpace (Spec.map f).toLRSHom.toShHom

/-- The canonical map from the base ring `R` to the global sections of the coefficient sheaf
on `Spec A`. -/
noncomputable abbrev affineBaseRingMap {R A : CommRingCat.{u}} (f : R ⟶ A) :
    R ⟶ RingedSpace.globalSectionsRing (affineCoefficientSpace f) :=
  (ΓSpecIso R).inv ≫
    (ModuleCech.relativeSpaceMap (Spec.map f).toLRSHom.toShHom).hom.c.app (Opposite.op ⊤)

/-- Derived global sections of the relative de Rham complex of `Spec A ⟶ Spec R`, with
scalars restricted along the canonical map from `R`. -/
noncomputable abbrev affineDerivedGlobalSections {R A : CommRingCat.{u}} (f : R ⟶ A) :
    DerivedCategory (ModuleCat.{u} R) :=
  (ModuleCat.derivedRestrictionOfScalars (affineBaseRingMap f).hom).obj
    ((RingedSpace.moduleDerivedGlobalSections (affineCoefficientSpace f)).obj
      ((CochainComplex.Nat.toDerived (affineCoefficientSpace f).Modules).obj
        (RingedSpace.DeRham.complex (Spec.map f).toLRSHom.toShHom)))

/-- The algebraic relative de Rham complex of `f : R ⟶ A`, regarded as an object of `D(R)`. -/
noncomputable abbrev algebraicDerivedComplex {R A : CommRingCat.{u}} (f : R ⟶ A) :
    DerivedCategory (ModuleCat.{u} R) :=
  (CochainComplex.Nat.toDerived (ModuleCat.{u} R)).obj (CommRingCat.DeRham.complex f)

/-- The degree-`i` affine relative de Rham hypercohomology over `R`. -/
noncomputable abbrev affineCohomology {R A : CommRingCat.{u}} (f : R ⟶ A) (i : ℤ) :
    ModuleCat.{u} R :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
    (affineDerivedGlobalSections f)

/-- The degree-`i` cohomology of the algebraic relative de Rham complex of `f : R ⟶ A`. -/
noncomputable abbrev algebraicCohomology {R A : CommRingCat.{u}} (f : R ⟶ A) (i : ℤ) :
    ModuleCat.{u} R :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
    (algebraicDerivedComplex f)

/-- Derived global sections of the relative de Rham complex of the affine-scheme morphism
`Spec A ⟶ Spec R` induced by `f : R ⟶ A` are isomorphic in `D(R)` to the algebraic relative
de Rham complex of `A` over `R`. -/
theorem affineDerivedGlobalSections_isomorphic {R A : CommRingCat.{u}} (f : R ⟶ A) :
    IsIsomorphic (affineDerivedGlobalSections f) (algebraicDerivedComplex f) := sorry

/-- Affine relative de Rham cohomology is isomorphic to the cohomology of the algebraic
relative de Rham complex. -/
theorem affineCohomology_isomorphic {R A : CommRingCat.{u}} (f : R ⟶ A) (i : ℤ) :
    IsIsomorphic (affineCohomology f i) (algebraicCohomology f i) := sorry

end AlgebraicGeometry.Scheme.DeRham
