/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Locus.WeaklyAssociated
import ReasLib.AlgebraicGeometry.Scheme.WeaklyAssociatedPoints.GenericPoints

/-!
# Flat morphisms of finite presentation

Flat morphisms locally of finite type over integral schemes are locally of finite presentation.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A flat morphism of schemes locally of finite type over an integral target is locally of finite
presentation. -/
instance instLocallyOfFinitePresentationOfFlatOfIsIntegral
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [Flat f] [IsIntegral S] :
    LocallyOfFinitePresentation f := sorry

end AlgebraicGeometry
