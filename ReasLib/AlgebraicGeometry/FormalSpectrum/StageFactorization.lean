/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Colimit
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.FactorThroughStage

/-!
# Quasi-compact factorization through formal-spectrum stages
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {S : Scheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
  [IsWeaklyAdmissibleRing A] (hA : Spec (.of A) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

/-- The functor-of-points cocone leg `yoneda.obj (Spec(A ⧸ I)) ⟶ Spf(A)`. -/
def spfStageι (I : WeakIdealOfDefinition A) :
    yoneda.obj (stage A hA I) ⟶ (spf A hA).obj :=
  toSheafify (Scheme.fppfTopology.over S) (yoneda.obj (stage A hA I)) ≫
    Sheaf.homEquiv (spfι A hA I)

/-- `spfStageι` is the sheafification unit postcomposed with the `spf` cocone
leg at `I`. -/
theorem spfStageι_eq (I : WeakIdealOfDefinition A) :
    spfStageι hA I =
      toSheafify (Scheme.fppfTopology.over S) (yoneda.obj (stage A hA I)) ≫
        Sheaf.homEquiv (spfι A hA I) := sorry

/-- A morphism from a quasi-compact scheme over `S` into `Spf(A)` factors
through `Spec(A ⧸ I)` for some weak ideal of definition `I`. -/
theorem exists_factorThroughStage_spf {T : Over S} [CompactSpace T.left]
    (ξ : yoneda.obj T ⟶ (spf A hA).obj) :
    ∃ (I : WeakIdealOfDefinition A) (g : yoneda.obj T ⟶ yoneda.obj (stage A hA I)),
      g ≫ spfStageι hA I = ξ := sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
