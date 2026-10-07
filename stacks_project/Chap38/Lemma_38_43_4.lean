module

public import stacks_project.Chap38.Lemma_38_43_3
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Eta.Derived.LocallyFree
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.IdealSheaf.Eta.Derived

universe u

/- Lemma 38.43.4: a good triple with a locally bounded finite locally free representative
has such a representative for its derived ideal-sheaf eta. -/
@[stacks 0GTX] #check
  (AlgebraicGeometry.Scheme.IsGoodTriple.existsEtaRepresentative :
    ∀ {X : Scheme.{u}} (D : X.IdealSheafData)
      [IsEffectiveCartierDivisor D.subschemeι]
      (M : RingedSpace.ModuleDerived X.toRingedSpace)
      (hM : RingedSpace.ModuleDerived.IsPerfect M)
      (hgood : AlgebraicGeometry.Scheme.IsGoodTriple D M)
      (hrep : ∃ P : CochainComplex X.toRingedSpace.Modules ℤ,
        IsIsomorphic (DerivedCategory.Q.obj P) M ∧
          RingedSpace.CochainComplex.IsLocallyBoundedAbove P ∧
          RingedSpace.CochainComplex.IsLocallyBoundedBelow P ∧
          ∀ i : ℤ, (SheafOfModules.IsFiniteLocallyFree
              (R := X.toRingedSpace.ringCatSheaf) :
            ObjectProperty X.toRingedSpace.Modules) (P.X i)),
      ∃ Q : CochainComplex X.toRingedSpace.Modules ℤ,
        IsIsomorphic (DerivedCategory.Q.obj Q) ((functor D.toSubobject).obj M) ∧
          RingedSpace.CochainComplex.IsLocallyBoundedAbove Q ∧
          RingedSpace.CochainComplex.IsLocallyBoundedBelow Q ∧
          ∀ i : ℤ, (SheafOfModules.IsFiniteLocallyFree
              (R := X.toRingedSpace.ringCatSheaf) :
            ObjectProperty X.toRingedSpace.Modules) (Q.X i))
