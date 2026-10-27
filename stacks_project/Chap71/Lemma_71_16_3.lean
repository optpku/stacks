/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.ClosedSubspace.Support

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open AlgebraicGeometry.AlgebraicSpace.Modules
open SheafOfModules.RingedSite

noncomputable section

universe u

/- Lemma 71.16.3
A finitely presented closed subspace of relative Proj avoiding a quasi-compact open
has a finite-type positive-degree quotient presentation supported away from that open.
-/
@[stacks 085N] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativeProj.existsQuotientByFiniteTypeDegreeSubobject_support_disjoint :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] [𝒜.IsQuasicoherent]
    {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) {Z : AlgebraicSpace S}
    (i : Z ⟶ toAlgebraicSpace F hF)
    [IsClosedImmersion i] [QuasiCompact (toAlgebraicSpace_hom F hF)]
    [FinitePresentation i] (hfinite : ∀ n : ℕ, (deg.obj n).IsFiniteType)
    (U : OpenSubspace X) [IsQuasiCompact U.X]
    (hdisjoint :
      Disjoint U.pointsSet
        (Set.range (Points.map (i ≫ toAlgebraicSpace_hom F hF)))),
    ∃ (d : ℕ) (G : Subobject (deg.obj d))
      (Q : ClosedSubspaceQuotient F hF i),
      0 < d ∧ G ∈ finiteTypeQuasiCoherentSubobjects (deg.obj d) ∧
        Q.IsQuotientByDegreeSubobject d G ∧
          Disjoint (moduleSupport (cokernel G.arrow)) U.pointsSet)
