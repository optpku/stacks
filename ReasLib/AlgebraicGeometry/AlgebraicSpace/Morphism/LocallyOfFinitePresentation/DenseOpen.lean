/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.SchemeTheoreticDensity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.DenseOpen

/-!
# Extending local finite presentation from a dense open of algebraic spaces

A flat morphism of algebraic spaces that is locally of finite type is locally
of finite presentation when its restriction to a quasi-compact
scheme-theoretically dense open of the target is locally of finite
presentation.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale.LocallyOfFinitePresentation

variable {S : Scheme.{u}} {X Y V : AlgebraicSpace S}

/-- A flat, locally-of-finite-type morphism of algebraic spaces is locally of
finite presentation when its restriction to a quasi-compact
scheme-theoretically dense open subspace is locally of finite presentation. -/
theorem of_restrict_of_flat (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
    (ι : V ⟶ Y) (h_open : Representable.IsOpenImmersion ι)
    (h_quasiCompact : Representable.QuasiCompact ι)
    (h_dense : Open.IsSchemeTheoreticallyDense ι)
    (h_restrict : LocallyOfFinitePresentation (Open.inverseImageTo f ι h_open)) :
    LocallyOfFinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtale.LocallyOfFinitePresentation
