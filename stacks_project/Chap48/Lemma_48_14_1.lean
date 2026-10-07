module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.EffectiveCartierDuality
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 48.14.1: for an effective Cartier divisor `i : D ⟶ X`, the right-adjoint
derived internal Hom `Rℓom(𝒪_D, 𝒪_X)` is canonically isomorphic in `D(𝒪_D)` to the
normal sheaf of `i`, placed in degree `1`. -/
@[stacks 0B4B] #check
  (AlgebraicGeometry.Scheme.rHomStructureSheaf_isomorphic_normalSheaf_shift :
    ∀ {X D : Scheme.{u}} (i : D ⟶ X) [IsEffectiveCartierDivisor i]
      (rHomOD : RingedSpace.ModuleDerived X.toRingedSpace ⥤
        RingedSpace.ModuleDerived D.toRingedSpace)
      (rHomODAdjunction : RingedSpace.moduleDerivedPushforward i.toShHom ⊣ rHomOD),
      IsIsomorphic
        (rHomOD.obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj
            (SheafOfModules.unit X.ringCatSheaf)))
        (((DerivedCategory.singleFunctor D.Modules 0).obj
          (AlgebraicGeometry.Scheme.Hom.normalSheaf i))⟦(-1 : ℤ)⟧))
