module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Perfect.TensorAnnihilator

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.MonoidalCategory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DerivedQCoh
namespace SupportedOn

/- Lemma 36.17.5: a map from a perfect object, or from a pseudo-coherent object to a
bounded-below object, supported on `T` is annihilated after tensoring by a perfect object
mapping to the derived tensor unit, and that map becomes an isomorphism away from `T`. -/
@[stacks 0A9C] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn.existsTensorAnnihilator :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
      (T : TopologicalSpace.Closeds X) (hT : IsCompact (T.compl : Set X))
      (P : Scheme.ModuleDerived.Quasicoherent X) (E : SupportedOn X T)
      (α : P ⟶ (inclusion X T).obj E)
      (h : RingedSpace.ModuleDerived.IsPerfect P.obj ∨
        (RingedSpace.ModuleDerived.IsPseudoCoherent P.obj ∧
          (t.plus : ObjectProperty
            (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj.obj)),
      ∃ (I : RingedSpace.ModuleDerived X.toRingedSpace)
        (i : I ⟶ 𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace)),
        RingedSpace.ModuleDerived.IsPerfect I ∧
          (i ⊗ₘ 𝟙 P.obj) ≫ (λ_ P.obj).hom ≫
            (Scheme.ModuleDerived.Quasicoherent.inclusion X).map α = 0 ∧
          IsIso ((RingedSpace.moduleRestrictionToOpenDerived
            X.toRingedSpace T.compl).map i))

end SupportedOn
end DerivedQCoh
end Scheme
end AlgebraicGeometry
