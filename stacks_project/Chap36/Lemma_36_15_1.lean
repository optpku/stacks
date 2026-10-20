module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Extension.Support
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.Hom.IsFlat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.15.1: a perfect derived module on a quasi-compact open subscheme of a
quasi-compact quasi-separated scheme is a retract of the restriction of a globally
perfect derived module. -/
@[stacks 09IQ] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.exists_retract_extension_of_isPerfect :
    ∀ {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (P : RingedSpace.ModuleDerived U.toRingedSpace)
      (hP : RingedSpace.ModuleDerived.IsPerfect P),
      ∃ R : RingedSpace.ModuleDerived X.toRingedSpace,
        RingedSpace.ModuleDerived.IsPerfect R ∧
          Nonempty (CategoryTheory.Retract P
            ((exactPullback j.toShHom).mapDerivedCategory.obj R)))

end AlgebraicGeometry.Scheme.DerivedQCoh
