/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.Topology.Sheaf.Cohomology.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Differentials
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Properties
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.Genus
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ProjectiveLine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
open scoped AlgebraicGeometry

universe u

/- Exercise 111.63.2 (Theorems) (1): on a Noetherian space of Krull dimension at most `d`,
abelian sheaf cohomology vanishes in degrees `p > d`. -/
@[stacks 0G14] #check
  (CategoryTheory.Sheaf.isZero_higherCohomology_of_noetherianSpace_of_topologicalKrullDim_le :
    ∀ {X : TopCat.{u}} [NoetherianSpace X]
      [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
      [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] (d : ℕ),
      topologicalKrullDim X ≤ d →
        ∀ (F : X.Sheaf AddCommGrpCat.{u}) {p : ℕ}, d < p →
          IsZero (F.H' p (⊤ : Opens X)))

/- Exercise 111.63.2 (Theorems) (2): the sheaf of relative differentials of a smooth morphism
is finite locally free. -/
@[stacks 0G14] #check
  (AlgebraicGeometry.Smooth.differentials_isFiniteLocallyFree :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S), Smooth f →
      (Ω[f.toShHom]).IsFiniteLocallyFree)

/- Exercise 111.63.2 (Theorems) (3): the dualizing module of a smooth proper morphism of
relative dimension `d` is isomorphic to `Λ[d] Ω[f.toShHom]`. -/
@[stacks 0G14] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.smooth_dualizingModule_isomorphic_exteriorPower :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (d : ℕ)
      [SmoothOfRelativeDimension d f],
      IsIsomorphic
        (ProperDualizingComplex.dualizingModule f)
        (RingedSpace.ExteriorPower.sheaf (Ω[f.toShHom]) d))

/- Exercise 111.63.2 (Theorems) (4): a smooth proper genus 0 curve over an algebraically
closed field is isomorphic to `ProjectiveLine`. -/
@[stacks 0G14] #check
  (AlgebraicGeometry.SchemeOverField.iso_projectiveLine_of_genus_zero :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Curve X] [IsProper X.hom] [Smooth X.hom],
      Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 0 →
      Nonempty (X ≅ Over.mk (ProjectiveLine.toSpec k)))

/- Exercise 111.63.2 (Theorems) (5): the genus of a nonempty equidimensional plane curve with
no embedded points is `((F.totalDegree - 1) * (F.totalDegree - 2)) / 2`. -/
@[stacks 0G14] #check
  (AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.planeCurve_genus_eq_totalDegree :
    ∀ (k : Type u) [Field k]
    (Z : (ProjectiveSpace.scheme k 2).IdealSheafData)
    [Nonempty Z.subscheme]
    (P : ProjTwistPresentation (ProjectiveSpace.grading k 2))
    [h_componentDim : Fact (∀ C : irreducibleComponents Z.subscheme,
      topologicalKrullDim (C : Set Z.subscheme) = 1)]
    [h_noEmbeddedPoints : Fact (Z.subscheme.embeddedPoints = (∅ : Set Z.subscheme))]
    (F : MvPolynomial (Fin 3) k)
    (h_generator : (twistIdeal 2 Z P).toIdeal = Ideal.span {F}),
    Scheme.Hom.cohomologyFinrank
      (Z.subschemeι ≫ ProjectiveSpace.toSpec k 2)
      (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules) 1 =
      ((F.totalDegree - 1) * (F.totalDegree - 2)) / 2)
