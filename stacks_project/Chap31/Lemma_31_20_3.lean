module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Regularity.Implications
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 31.20.3 (1): for a ringed space, a regular sheaf of ideals is Koszul-regular. -/
@[stacks 063E] #check
  (@AlgebraicGeometry.RingedSpace.IsRegularIdealSheaf.isKoszulRegular :
    ∀ {X : AlgebraicGeometry.RingedSpace.{u}}
      (I : CategoryTheory.Subobject (SheafOfModules.unit X.ringCatSheaf)),
      [AlgebraicGeometry.RingedSpace.IsRegularIdealSheaf I] →
        AlgebraicGeometry.RingedSpace.IsKoszulRegularIdealSheaf I)

/- Lemma 31.20.3 (2): for a ringed space, a Koszul-regular sheaf of ideals is
`H₁`-regular. -/
@[stacks 063E] #check
  (@AlgebraicGeometry.RingedSpace.IsKoszulRegularIdealSheaf.isH1Regular :
    ∀ {X : AlgebraicGeometry.RingedSpace.{u}}
      (I : CategoryTheory.Subobject (SheafOfModules.unit X.ringCatSheaf)),
      [AlgebraicGeometry.RingedSpace.IsKoszulRegularIdealSheaf I] →
        AlgebraicGeometry.RingedSpace.IsH1RegularIdealSheaf I)

/- Lemma 31.20.3 (3): for a ringed space, an `H₁`-regular sheaf of ideals is
quasi-regular. -/
@[stacks 063E] #check
  (@AlgebraicGeometry.RingedSpace.IsH1RegularIdealSheaf.isQuasiRegular :
    ∀ {X : AlgebraicGeometry.RingedSpace.{u}}
      (I : CategoryTheory.Subobject (SheafOfModules.unit X.ringCatSheaf)),
      [AlgebraicGeometry.RingedSpace.IsH1RegularIdealSheaf I] →
        AlgebraicGeometry.RingedSpace.IsQuasiRegularIdealSheaf I)
