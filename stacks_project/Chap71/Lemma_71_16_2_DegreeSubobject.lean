/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.ClosedSubspace.DegreeSubobject

/-!
# Quotients of relative Proj by a finite-type degree subobject

A closed subspace of `underline{Proj}_X(𝒜)` is cut out by a single
nonnegative degree subobject `G ⊂ 𝒜_d` when the corresponding quotient
presentation is universal among graded-algebra maps that kill `G`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.ClosedSubspaceQuotient.IsQuotientByDegreeSubobject :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
      [𝒜.IsCommutative] [𝒜.IsQuasicoherent]
      {deg : DegreePieces 𝒜} {F : ProjFunctor X 𝒜}
      {hF : F.IsAssociatedToQuadruples deg}
      {Z : AlgebraicSpace S} {i : Z ⟶ toAlgebraicSpace F hF}
      [IsClosedImmersion i]
      (Q : ClosedSubspaceQuotient F hF i) (d : ℕ) (G : Subobject (deg.obj d)), Prop)
