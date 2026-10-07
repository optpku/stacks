module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.ExternalTensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Generated

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory.ObjectProperty.GeneratedNotation

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a quasi-compact separated smooth scheme over a field, there exist finite locally free
modules `E` and `G` whose external tensor product generates the diagonal structure module
in the derived category of the fiber product. -/
theorem exists_externalTensorProduct_mem_generated
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [IsSeparated f] [Smooth f] :
    ∃ (E : X.Modules) (_ : E.IsFiniteLocallyFree)
      (G : X.Modules) (_ : G.IsFiniteLocallyFree),
      ObjectProperty.Generated.property
        ((DerivedCategory.singleFunctor ((Limits.pullback f f).Modules) 0).obj
          (externalTensorProduct f f E G))
        ((DerivedCategory.singleFunctor ((Limits.pullback f f).Modules) 0).obj
          (Scheme.Hom.pushforwardStructureModule (Limits.pullback.diagonal f))) := sorry

end AlgebraicGeometry.Scheme.Modules
