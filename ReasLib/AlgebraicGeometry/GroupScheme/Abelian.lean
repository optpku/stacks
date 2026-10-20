module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.GroupScheme

/-!
# Abelian schemes

Abelian schemes are flat proper group schemes of finite presentation with
geometrically integral fibres.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.GroupScheme

/-- An abelian scheme is a flat proper group scheme of finite presentation
with geometrically integral structure morphism. -/
class AbelianScheme {S : Scheme.{u}} (G : GroupScheme S) : Prop where
  [isFlat : AlgebraicGeometry.Flat G.X.hom]
  [isProper : AlgebraicGeometry.IsProper G.X.hom]
  [locallyOfFinitePresentation : AlgebraicGeometry.LocallyOfFinitePresentation G.X.hom]
  [geometricallyIntegral : GeometricallyIntegral G.X.hom]

/-- A flat proper finite-presentation group scheme with geometrically integral
structure morphism is an abelian scheme. -/
instance instAbelianScheme {S : Scheme.{u}} (G : GroupScheme S)
    [AlgebraicGeometry.Flat G.X.hom] [AlgebraicGeometry.IsProper G.X.hom]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.X.hom]
    [GeometricallyIntegral G.X.hom] : AbelianScheme G where

/-- A group scheme is abelian exactly when it is flat, proper, locally of finite
presentation, and has geometrically integral fibres. -/
theorem abelianScheme_iff {S : Scheme.{u}} (G : GroupScheme S) :
    AbelianScheme G ↔
      AlgebraicGeometry.Flat G.X.hom ∧ AlgebraicGeometry.IsProper G.X.hom ∧
        AlgebraicGeometry.LocallyOfFinitePresentation G.X.hom ∧
          ∀ s : S, GeometricallyIntegral (G.X.hom.fiberToSpecResidueField s) :=
  sorry

/-- The group object underlying an abelian scheme is commutative. -/
instance instIsCommMonObj {S : Scheme.{u}} (G : GroupScheme S) [AbelianScheme G] :
    IsCommMonObj G.X where
  mul_comm := sorry

end AlgebraicGeometry.GroupScheme
