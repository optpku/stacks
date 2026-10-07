module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Extension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.13.7: a morphism between the restrictions of a perfect object and an
arbitrary object of `D_QCoh(𝒪_X)` to a quasi-compact open subscheme of an affine scheme
factors through the restriction of a perfect object `tensorObj E I`, where `I` is perfect
and the map `tensorObj E I ⟶ E` restricts to an isomorphism. -/
@[stacks 08EH] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.exists_tensorFactorization_of_isPerfect :
    ∀ {X U : Scheme.{u}} [IsAffine X]
      (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (E E' : DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
      (_ : RingedSpace.ModuleDerived.IsPerfect E.obj)
      (α : (OpenImmersion.pullback j).obj E ⟶ (OpenImmersion.pullback j).obj E'),
      ∃ (I : DerivedCategory.CohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
        (_ : RingedSpace.ModuleDerived.IsPerfect I.obj)
        (_ : RingedSpace.ModuleDerived.IsPerfect (tensorObj E I).obj)
        (β : tensorObj E I ⟶ E) (γ : tensorObj E I ⟶ E'),
        IsIso ((OpenImmersion.pullback j).map β) ∧
          (OpenImmersion.pullback j).map β ≫ α =
            (OpenImmersion.pullback j).map γ)

end AlgebraicGeometry.Scheme.DerivedQCoh
