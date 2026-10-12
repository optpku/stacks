/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.FiberFinrank

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 36.32.1 (1): formation of the fiber-cohomology finrank function commutes
with arbitrary cartesian base change. -/
@[stacks 0BDN] #check
  (AlgebraicGeometry.Scheme.Hom.fiberCohomologyFinrank_baseChange :
    ∀ {X' X S' S : Scheme.{u}}
      (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
      [IsProper f] [Scheme.Hom.FinitePresentation f]
      (ℱ : X.Modules) [ℱ.IsFinitePresentation] [SheafOfModules.IsFlatOver ℱ f.toShHom]
      (sq : IsPullback g' f' f g) (i : ℤ),
      Scheme.Hom.fiberCohomologyFinrank f' ((Scheme.Modules.pullback g').obj ℱ) i =
        fun s' : S' ↦ Scheme.Hom.fiberCohomologyFinrank f ℱ i (g s'))

/- Lemma 36.32.1 (2): every fiber-cohomology finrank function is upper
semicontinuous. -/
@[stacks 0BDN] #check
  (AlgebraicGeometry.Scheme.Hom.fiberCohomologyFinrank_upperSemicontinuous :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Scheme.Hom.FinitePresentation f]
      (ℱ : X.Modules) [ℱ.IsFinitePresentation] [SheafOfModules.IsFlatOver ℱ f.toShHom]
      (i : ℤ),
      UpperSemicontinuous (Scheme.Hom.fiberCohomologyFinrank f ℱ i))

/- Lemma 36.32.1 (3): every level set of a fiber-cohomology finrank function is
locally constructible. -/
@[stacks 0BDN] #check
  (AlgebraicGeometry.Scheme.Hom.fiberCohomologyFinrank_levelSet_isLocallyConstructible :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Scheme.Hom.FinitePresentation f]
      (ℱ : X.Modules) [ℱ.IsFinitePresentation] [SheafOfModules.IsFlatOver ℱ f.toShHom]
      (i : ℤ) (n : ℕ),
      Topology.IsLocallyConstructible
        ((Scheme.Hom.fiberCohomologyFinrank f ℱ i) ⁻¹' {n}))
