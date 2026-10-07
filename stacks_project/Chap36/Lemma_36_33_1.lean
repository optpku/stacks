module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Coherent

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 36.33.1: if `R` is coherent, `X` is of finite presentation over `R`, and `G` is
finitely presented and flat over `R` with proper support over `R`, then every
`H^i(X, G)` is a coherent `R`-module. -/
@[stacks 0EX6] #check
  (AlgebraicGeometry.Scheme.Hom.cohomologyCoherent :
    ∀ {R : Type u} [CommRing R] [IsCoherentRing R] {X : Scheme.{u}}
      [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
      (f : X ⟶ Spec (CommRingCat.of R)) [Scheme.Hom.FinitePresentation f]
      (G : X.Modules) [G.IsFinitePresentation] [SheafOfModules.IsFlatOver G f.toShHom]
      [Scheme.Modules.HasProperSupportOver f G] (i : ℕ),
      Module.Coherent R (AlgebraicGeometry.Scheme.Hom.cohomology f G i))
