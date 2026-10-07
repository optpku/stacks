module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.GroupScheme

/-!
# Abelian schemes

An abelian scheme over a base is a flat proper group scheme of finite presentation
whose fibres are abelian varieties, recorded here as a geometrically integral
structure morphism (equivalently, geometrically integral fibres).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.GroupScheme

/-- An abelian scheme over a base scheme `S` is a flat proper group scheme of
finite presentation over `S` all of whose fibres are abelian varieties, in the
sense that the structure morphism is geometrically integral. -/
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

/-- Unfold `AbelianScheme G` into flatness, properness, local finite presentation,
and geometrically integral fibres. -/
theorem abelianScheme_iff {S : Scheme.{u}} (G : GroupScheme S) :
    AbelianScheme G ↔
      AlgebraicGeometry.Flat G.X.hom ∧ AlgebraicGeometry.IsProper G.X.hom ∧
        AlgebraicGeometry.LocallyOfFinitePresentation G.X.hom ∧
          ∀ s : S, GeometricallyIntegral (G.X.hom.fiberToSpecResidueField s) :=
  sorry

/-- The group object underlying an abelian scheme is commutative. -/
instance instIsCommMonObj {S : Scheme.{u}} (G : GroupScheme S) [AbelianScheme G] :
    IsCommMonObj G.X :=
  sorry

/-- Fibres of an abelian scheme are geometrically integral over the residue field. -/
instance instGeometricallyIntegral_fiber {S : Scheme.{u}} (G : GroupScheme S)
    [AbelianScheme G] (s : S) :
    GeometricallyIntegral (G.X.hom.fiberToSpecResidueField s) :=
  sorry

end AlgebraicGeometry.GroupScheme
