module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.CategoryTheory.DerivedCategory.InjectiveAmplitude
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

universe u

/-- A derived module complex on a ringed space is dualizing when it is pseudo-coherent,
has finite injective dimension, and its canonical homothety is invertible. -/
structure IsDualizingComplex {X : RingedSpace.{u}} (K : ModuleDerived X)
    [MonoidalCategory (ModuleDerived X)] (H : MonoidalClosed (ModuleDerived X)) : Prop where
  /-- A dualizing complex is pseudo-coherent. -/
  pseudoCoherent : K.IsPseudoCoherent
  /-- A dualizing complex has finite injective dimension. -/
  finiteInjectiveDimension : DerivedCategory.HasFiniteInjectiveDimension K
  /-- The canonical homothety from the tensor unit to `RHom(K, K)` is invertible. -/
  homothetyIsIso :
    IsIso (@MonoidalClosed.curry' (ModuleDerived X) _ _ K K (H.closed K) (𝟙 K))

namespace IsDualizingComplex

/-- Construct the dualizing-complex property from its three defining conditions. -/
def ofConditions {X : RingedSpace.{u}} {K : ModuleDerived X}
    [MonoidalCategory (ModuleDerived X)] {H : MonoidalClosed (ModuleDerived X)}
    (hPseudoCoherent : K.IsPseudoCoherent)
    (hFiniteInjectiveDimension : DerivedCategory.HasFiniteInjectiveDimension K)
    (hHomothety :
      IsIso (@MonoidalClosed.curry' (ModuleDerived X) _ _ K K (H.closed K) (𝟙 K))) :
    K.IsDualizingComplex H := sorry

end IsDualizingComplex

/-- The three defining conditions for a dualizing complex on a ringed space. -/
theorem isDualizingComplex_iff {X : RingedSpace.{u}} (K : ModuleDerived X)
    [MonoidalCategory (ModuleDerived X)] (H : MonoidalClosed (ModuleDerived X)) :
    K.IsDualizingComplex H ↔
      K.IsPseudoCoherent ∧ DerivedCategory.HasFiniteInjectiveDimension K ∧
        IsIso (@MonoidalClosed.curry' (ModuleDerived X) _ _ K K (H.closed K) (𝟙 K)) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
