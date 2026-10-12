/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.ProjectiveDeformation

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveDeformation

/- Lemma 37.10.6 (Deformations of projective schemes): a proper, flat, finitely presented
morphism carrying a relatively ample invertible module over a quasi-compact base has a uniform
cutoff for compatible relative-Proj presentations of all deformations across thickenings,
together with compatible base-change data. -/
@[stacks 0D4F] #check
  (AlgebraicGeometry.ProjectiveDeformation.existsPresentationBound :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f]
      [Scheme.Hom.FinitePresentation f] [CompactSpace S]
      (L : X.Modules) [RelativelyAmple f L],
      ∃ d₀ : ℕ,
        ∀ {X' S' : Scheme.{u}} (iX : X ⟶ X') (f' : X' ⟶ S') (i : S ⟶ S')
          [IsThickening i] [IsProper f'] [Flat f'] [Scheme.Hom.FinitePresentation f'],
          IsPullback f iX i f' →
            ∀ (L' : X'.Modules) [Scheme.Modules.Invertible L'],
              (L ≅ (Scheme.Modules.pullback iX).obj L') →
                ∃ Q : Presentation d₀ f' L',
                  ∀ {T : Scheme.{u}} (h : T ⟶ S'),
                    Nonempty (Presentation.BaseChange Q h))

end AlgebraicGeometry.ProjectiveDeformation
