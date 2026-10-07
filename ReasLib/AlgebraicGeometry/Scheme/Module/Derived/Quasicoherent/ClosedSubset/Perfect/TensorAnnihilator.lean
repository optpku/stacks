module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.Finiteness
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Perfect.Compact
public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Resolution
public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Factorization
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Homological.SelectedCoproduct

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.MonoidalCategory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
  [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
  [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]

/-- A morphism from a perfect complex, or from a pseudo-coherent complex to a bounded-below
complex, with target supported on a closed subset is annihilated after tensoring by a perfect
complex whose map to the tensor unit is invertible away from that subset. -/
@[stacks 0A9C]
theorem existsTensorAnnihilator (T : TopologicalSpace.Closeds X)
    (hT : IsCompact (T.compl : Set X)) (P : Scheme.ModuleDerived.Quasicoherent X)
    (E : SupportedOn X T) (α : P ⟶ (inclusion X T).obj E)
    (h : RingedSpace.ModuleDerived.IsPerfect P.obj ∨
      (RingedSpace.ModuleDerived.IsPseudoCoherent P.obj ∧
        (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj.obj)) :
    ∃ (I : RingedSpace.ModuleDerived X.toRingedSpace)
      (i : I ⟶ 𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace)),
      RingedSpace.ModuleDerived.IsPerfect I ∧
        (i ⊗ₘ 𝟙 P.obj) ≫ (λ_ P.obj).hom ≫
          (Scheme.ModuleDerived.Quasicoherent.inclusion X).map α = 0 ∧
        IsIso ((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace T.compl).map i) := sorry

/-- A morphism from a perfect complex to a complex supported on a closed subset is annihilated
after tensoring by a perfect complex whose map to the tensor unit is invertible away from that
subset. -/
theorem existsTensorAnnihilator_of_isPerfect (T : TopologicalSpace.Closeds X)
    (hT : IsCompact (T.compl : Set X)) (P : Scheme.ModuleDerived.Quasicoherent X)
    (E : SupportedOn X T) (α : P ⟶ (inclusion X T).obj E)
    (hP : RingedSpace.ModuleDerived.IsPerfect P.obj) :
    ∃ (I : RingedSpace.ModuleDerived X.toRingedSpace)
      (i : I ⟶ 𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace)),
      RingedSpace.ModuleDerived.IsPerfect I ∧
        (i ⊗ₘ 𝟙 P.obj) ≫ (λ_ P.obj).hom ≫
          (Scheme.ModuleDerived.Quasicoherent.inclusion X).map α = 0 ∧
        IsIso ((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace T.compl).map i) := sorry

/-- A morphism from a pseudo-coherent complex to a bounded-below complex supported on a closed
subset is annihilated after tensoring by a perfect complex whose map to the tensor unit is
invertible away from that subset. -/
theorem existsTensorAnnihilator_of_isPseudoCoherent (T : TopologicalSpace.Closeds X)
    (hT : IsCompact (T.compl : Set X)) (P : Scheme.ModuleDerived.Quasicoherent X)
    (E : SupportedOn X T) (α : P ⟶ (inclusion X T).obj E)
    (hP : RingedSpace.ModuleDerived.IsPseudoCoherent P.obj)
    (hE : (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj.obj) :
    ∃ (I : RingedSpace.ModuleDerived X.toRingedSpace)
      (i : I ⟶ 𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace)),
      RingedSpace.ModuleDerived.IsPerfect I ∧
        (i ⊗ₘ 𝟙 P.obj) ≫ (λ_ P.obj).hom ≫
          (Scheme.ModuleDerived.Quasicoherent.inclusion X).map α = 0 ∧
        IsIso ((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace T.compl).map i) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn
