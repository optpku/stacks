module

public import Mathlib.Data.Countable.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentData.Effectivity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

/-!
# Effective descent along fppf coverings of algebraic spaces

Descent data along countable fppf coverings are effective. Descent data with
finite-type component structure morphisms are effective along arbitrary fppf coverings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.DescentData

/-- Every descent datum along a countable fppf covering of algebraic spaces
over a scheme is effective. -/
theorem isEffective_of_countable {I : Type v} [Countable I] {S : Scheme.{u}}
    {X : AlgebraicSpace S} (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)
    [FppfCovering Xᵢ f] (D : DescentData Xᵢ f) : D.IsEffective :=
  sorry

/-- A descent datum along an fppf covering of algebraic spaces over a scheme
is effective if each component structure morphism is of finite type. -/
theorem isEffective_of_finiteType {I : Type v} {S : Scheme.{u}}
    {X : AlgebraicSpace S} (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)
    [FppfCovering Xᵢ f] (D : DescentData Xᵢ f)
    (h_finiteType : ∀ i, FiniteType (D.obj i).hom) : D.IsEffective :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DescentData
