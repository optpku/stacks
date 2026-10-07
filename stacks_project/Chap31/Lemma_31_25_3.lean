module

public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Meromorphic
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 31.25.3 (1): on an integral scheme, the sheaf of meromorphic functions is isomorphic
to the constant sheaf with value the function field. -/
@[stacks 01X5] #check
  (AlgebraicGeometry.Scheme.meromorphicFunctionSheaf_isIsomorphic_constantFunctionField :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X],
      CategoryTheory.IsIsomorphic X.meromorphicFunctionSheaf
        ((CategoryTheory.constantSheaf
          (Opens.grothendieckTopology X.toTopCat) CommRingCat).obj
            X.functionField))

/- Lemma 31.25.3 (2): on an integral scheme, the underlying additive sheaf of meromorphic
sections of a quasicoherent module is isomorphic to the constant sheaf with value its stalk at
the generic point. -/
@[stacks 01X5] #check
  (AlgebraicGeometry.Scheme.meromorphicSectionSheaf_underlying_isIsomorphic_constantGenericStalk :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      CategoryTheory.IsIsomorphic
        ((SheafOfModules.toSheaf
          (SheafOfModules.RingedSite.ringSheaf
            (Opens.grothendieckTopology X.toTopCat)
              X.meromorphicFunctionSheaf)).obj
                (X.meromorphicSectionSheaf ℱ))
        ((CategoryTheory.constantSheaf
          (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat).obj
            (AddCommGrpCat.of
              (AlgebraicGeometry.RingedSpace.stalkModuleCat ℱ
                (genericPoint X)))))
