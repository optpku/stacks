/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Target
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.HigherDirectImage
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]

/-- Lemma 59.92.2: if `f : X ⟶ Y` is a proper morphism of schemes all of whose
scheme-theoretic fibres have dimension `≤ n`, then for any abelian torsion sheaf
`F` on `X` étale we have `higherDirectImage (smallEtalePullback f) F q = 0` for
`q > 2n`. The fibre bound is `∀ y, f.fiberDimension y ≤ n`, equivalently
`topologicalKrullDim (f.fiber y) ≤ n`. -/
@[stacks 095U]
theorem higherDirectImage_isZero_of_isProper_fiberDimension_le
    {n : ℕ} (hdim : ∀ y : Y, f.fiberDimension y ≤ (n : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (hF : IsLocallyTorsion F)
    {q : ℕ} (hq : 2 * n < q) :
    IsZero (higherDirectImage (smallEtalePullback f) F q :
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end

end
