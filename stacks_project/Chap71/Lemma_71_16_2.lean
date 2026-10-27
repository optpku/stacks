/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.ClosedSubspace.DegreeSubobject
import StacksCheckRecall

/-!
# Lemma 71.16.2

A finitely presented closed subspace of relative Proj of a quasi-coherent
graded algebra on a quasi-compact quasi-separated algebraic space is itself
relative Proj of the quotient by a finite-type quasi-coherent submodule in
one positive degree.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open AlgebraicGeometry.AlgebraicSpace.Modules
open SheafOfModules.RingedSite

noncomputable section

universe u

/- Lemma 71.16.2
Let `S` be a scheme and let `X` be a quasi-compact quasi-separated algebraic
space over `S`. Let `𝒜` be a quasi-coherent graded `𝒪_X`-algebra, and let
`π : P = underline{Proj}_X(𝒜) ⟶ X` be the relative Proj of `𝒜`. Let
`i : Z ⟶ P` be a closed subspace. If `π` is quasi-compact and `i` is of
finite presentation, then there exist `d > 0` and a quasi-coherent finite
type `𝒪_X`-submodule `G ⊂ 𝒜_d` such that
`Z = underline{Proj}_X(𝒜 / G 𝒜)`. -/
@[stacks 085M]
#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.existsQuotientByFiniteTypeDegreeSubobject :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] [𝒜.IsQuasicoherent]
    {deg : DegreePieces 𝒜} (F : ProjFunctor X 𝒜)
    (hF : F.IsAssociatedToQuadruples deg) {Z : AlgebraicSpace S}
    (i : Z ⟶ toAlgebraicSpace F hF)
    [IsClosedImmersion i] [QuasiCompact (toAlgebraicSpace_hom F hF)]
    [FinitePresentation i],
    ∃ (d : ℕ) (G : Subobject (deg.obj d))
      (Q : ClosedSubspaceQuotient F hF i),
      0 < d ∧ G ∈ finiteTypeQuasiCoherentSubobjects (deg.obj d) ∧
        Q.IsQuotientByDegreeSubobject d G)
