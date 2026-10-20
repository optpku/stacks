module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.CategoryTheory.Monoidal.Invertible

/-! # Finite locally free modules and tensor products on algebraic spaces -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Invertible `𝒪_X`-modules are finite locally free. -/
instance instIsFiniteLocallyFree_of_isInvertibleObject {S : Scheme.{u}}
    {X : AlgebraicSpace S} (L : X.Modules) [isInvertibleObject L] :
    SheafOfModules.IsFiniteLocallyFree L :=
  sorry

/-- Finite locally free `𝒪_X`-modules are closed under tensor product. -/
instance instIsFiniteLocallyFree_tensor {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E L : X.Modules) [SheafOfModules.IsFiniteLocallyFree E]
    [SheafOfModules.IsFiniteLocallyFree L] :
    SheafOfModules.IsFiniteLocallyFree (E ⊗ L) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
