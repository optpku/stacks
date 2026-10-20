module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZeroDerivation
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor
public import ReasLib.CategoryTheory.Cofibered.FiberIsoClass

/-!
# Derivations acting on square-zero fibre classes

Pushforward along derivation-induced square-zero morphisms defines a map from
derivations to fibre isomorphism classes and an action on these classes. Under
Schlessinger's (H2), the map is linear and the action is translation by its value.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

noncomputable section

namespace CategoryTheory.Functor

variable [IsPredeformationCategory p]
variable (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V]
  [Module Λ V] [IsScalarTower Λ k V]

/-- A derivation determines a square-zero fibre class by pushing forward the unique
residue-fibre class along its associated morphism. -/
def isoClassOfDerivation (D : Derivation Λ k V) :
    (fiberIsoClassFunctor p).obj (squareZero Λ k V) :=
  (fiberIsoClassFunctor p).map (derivationToSquareZero D) (fiberResidueClass p)

/-- The class associated to a derivation is the class of the pushforward of any
residue-fibre object along its associated morphism. -/
theorem isoClassOfDerivation_apply (x0 : p.Fiber (residue Λ k)) (D : Derivation Λ k V) :
    isoClassOfDerivation p V D =
      Quotient.mk'' (pushforwardFiberObj p (cleavageOp p) (derivationToSquareZero D) x0) :=
  sorry

/-- A derivation acts on square-zero fibre classes by pushforward along its
square-zero automorphism. -/
def squareZeroDerivationAction (D : Derivation Λ k V)
    (x : (fiberIsoClassFunctor p).obj (squareZero Λ k V)) :
    (fiberIsoClassFunctor p).obj (squareZero Λ k V) :=
  (fiberIsoClassFunctor p).map (squareZeroAut D) x

/-- Acting on a represented fibre class gives the class of the pushforward of its
representative. -/
theorem squareZeroDerivationAction_mk (D : Derivation Λ k V)
    (x : p.Fiber (squareZero Λ k V)) :
    squareZeroDerivationAction p V D (Quotient.mk'' x) =
      Quotient.mk'' (pushforwardFiberObj p (cleavageOp p) (squareZeroAut D) x) :=
  sorry

variable [HasSchlessingerH2 (fiberIsoClassFunctor p)]

/-- The canonical map from derivations to square-zero fibre classes is linear when
the isomorphism-class functor satisfies Schlessinger's (H2). -/
theorem isoClassOfDerivation_isLinearMap :
    IsLinearMap k (isoClassOfDerivation p V) := sorry

/-- The canonical derivation map bundled as a linear map under Schlessinger's (H2). -/
def isoClassOfDerivationLinear :
    Derivation Λ k V →ₗ[k] (fiberIsoClassFunctor p).obj (squareZero Λ k V) :=
  IsLinearMap.mk' (isoClassOfDerivation p V) (isoClassOfDerivation_isLinearMap p V)

/-- The bundled derivation map evaluates to the canonical derivation fibre class. -/
theorem isoClassOfDerivationLinear_apply (D : Derivation Λ k V) :
    isoClassOfDerivationLinear p V D = isoClassOfDerivation p V D := rfl

/-- The derivation action is translation by the canonical derivation fibre class under
Schlessinger's (H2). -/
theorem squareZeroDerivationAction_eq_add (D : Derivation Λ k V)
    (x : (fiberIsoClassFunctor p).obj (squareZero Λ k V)) :
    squareZeroDerivationAction p V D x = x + isoClassOfDerivation p V D := sorry

end CategoryTheory.Functor

end
