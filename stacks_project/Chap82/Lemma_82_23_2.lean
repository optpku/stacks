/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.Definition_82_22_1_Gysin
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

/- Lemma 82.23.2: In Situation 82.2.1, for good `X / B` and a Definition 82.22.1
triple `(L, s, i : D ⟶ X)` with `D = Z(s)` and `i = zeroSchemeι L s`, the
cycle-level Gysin `Hom.gysin` factors through `RationalEquivalence.boundaries`
by `Hom.gysinCycleHom_mem_boundaries`, inducing the additive map
`Hom.chowGysin δ pX L s k : Hom.chowGroup pX δ (k + 1) →+
Hom.chowGroup (zeroSchemeι L s ≫ pX) δ k`.
On representatives, `Hom.chowGysin_chowMk` recovers `Hom.gysin`, which is
definitionally `chowGysin ∘ chowMk`. -/
@[stacks 0ERA]
#check
  (Hom.chowGysin :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B] (δ : Points B → ℤ)
      [IsDimensionFunction δ] {X : AlgebraicSpace S} (pX : X ⟶ B)
      [QuasiSeparated pX] [LocallyOfFiniteType pX] (L : X.Modules)
      [isInvertibleObject L] (s : L.sections) (k : ℤ),
      Hom.chowGroup pX δ (k + 1) →+
        Hom.chowGroup (zeroSchemeι L s ≫ pX) δ k)
