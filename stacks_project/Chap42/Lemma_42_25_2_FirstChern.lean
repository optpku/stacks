module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

#check
  (AlgebraicGeometry.Scheme.Modules.firstChernClassCap :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S)
      [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] (ℒ : X.Modules) [Invertible ℒ] (k : ℤ),
      CycleGroup X (p.relativeDimensionFunction δ) (k + 1) →+
        @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance k)

end AlgebraicGeometry.Scheme.Modules
