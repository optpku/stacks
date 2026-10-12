/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.LinearSeries.Pencil
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 53.3.4: the morphism to the projective line associated to a linear series
`g : LinearSeries X _ d 1` is either nonconstant of degree at most `d`, or factors through
a closed point; in the latter case the canonical map `k → Γ(X, 𝒪_X)` is not bijective. -/
@[stacks 0CCR] #check (AlgebraicGeometry.LinearSeries.morphismDichotomy :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [IsProper X.hom] [Scheme.Regular X.left] {d : ℕ}
    (g : LinearSeries X (topologicalKrullDim_eq_one X).le d 1)
    (b : Module.Basis (Fin 2) k g.sections)
    (φ : X ⟶ Over.mk (ProjectiveSpace.toSpec k 1))
    (α : (Scheme.Modules.pullback φ.left).obj
      (ProjectiveSpace.twistingSheaf k 1 1) ⟶ g.lineBundle)
    (hcoord : ∀ i : Fin 2,
      SheafOfModules.sectionsMap α
          (Scheme.Modules.sectionsPullback φ.left
            (ProjectiveSpace.twistingSheaf k 1 1)
            (ProjectiveSpace.coordinateTwistSection k 1 i)) =
        RingedSpace.sectionFromTop g.lineBundle (g.inclusion (b i))),
    (φ.left.IsNonconstant ∧
      ∃ hdom : IsDominant φ.left,
        @Scheme.Hom.inducedFunctionFieldDegree _ _ φ.left
          (inferInstance : IsIntegral X.left)
          (inferInstance : IsIntegral (ProjectiveSpace.scheme k 1)) hdom ≤ d) ∨
      ((∃ (x : ProjectiveSpace.scheme k 1)
          (_ : IsClosed ({x} : Set (ProjectiveSpace.scheme k 1)))
          (ψ : X.left ⟶ Spec ((ProjectiveSpace.scheme k 1).residueField x)),
          ψ ≫ (ProjectiveSpace.scheme k 1).fromSpecResidueField x = φ.left) ∧
        ¬ Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)))
