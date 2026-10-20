module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Representability
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.Scheme.GRingStalks
import Mathlib.Tactic.CrossRefAttribute

/-!
# Representability of the proper-support Quot functor
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- The proper-support Quot functor of a quasi-coherent module along a finitely
presented separated morphism of algebraic spaces is represented by an algebraic
space over the base. -/
@[stacks 09TU]
theorem quot_isAlgebraicSpaceOver {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [FinitePresentation f] [Separated f] (F : X.Modules)
    [F.IsQuasicoherent] : IsAlgebraicSpaceOver (quot f F) := sorry

/-- The proper-support Quot functor of a finitely presented quasi-coherent module
along a finitely presented separated morphism of algebraic spaces is represented
by an algebraic space locally of finite presentation over the base. -/
@[stacks 09TU]
theorem quot_isLocallyOfFinitePresentationOver {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] :
    IsLocallyOfFinitePresentationOver (quot f F) := sorry

/-- Over a Noetherian scheme whose local rings are G-rings, the proper-support
Quot functor of a finitely presented quasi-coherent module flat over the base,
along a finitely presented separated structure morphism, is represented by an
algebraic space locally of finite presentation over the base. -/
@[stacks 0CZW]
theorem isLocallyOfFinitePresentationOver_of_artinAxioms
    {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] [HasGRingStalks S]
    {X : AlgebraicSpace S} (f : X ⟶ ofOver (Over.mk (𝟙 S)))
    [FinitePresentation f] [Separated f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hF_flat : Modules.flatOver F f) :
    IsLocallyOfFinitePresentationOver (quot f F) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
