/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.RingTheory.Regular.GRing
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.Definition_98_5_1
public import stacks_project.Chap98.Definition_98_9_4_Effective
public import stacks_project.Chap98.Definition_98_11_1_LimitPreserving
public import stacks_project.Chap98.Definition_98_13_1_Openness
public import stacks_project.Chap98.Lemma_98_13_8_Predeformations
public import stacks_project.Chap98.Lemma_98_13_8_SmoothYoneda
import Mathlib.Tactic.CrossRefAttribute

/-!
# Smooth finite-type 2-Yoneda approximations from Artin's axioms

If `S` is locally Noetherian, `X` is a category fibred in groupoids over
`(Sch/S)_fppf` whose diagonal is representable by algebraic spaces, and `X`
satisfies axioms [1], [2], [3], effectiveness of formal objects, and openness
of versality, then every finite-type residue object over a G-ring stalk is
approximated by a smooth finite-type 2-Yoneda 1-morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Lemma 98.13.8: let `S` be a locally Noetherian scheme, let `X` be a category
fibred in groupoids over `(Sch/S)_fppf`, and let `k` be a finite type field over
`S` with an object `x0` of `X` over `Spec(k)` with image `s`. Assume the
diagonal `Δ : X ⟶ X × X` is representable by algebraic spaces, `X` satisfies
axioms [1], [2], [3], every formal object of `X` is effective, openness of
versality holds for `X`, and `𝒪_{S,s}` is a G-ring. Then there exist a finite
type morphism `U ⟶ S` and an object `x` of `X` over `U` such that the 2-Yoneda
1-morphism `(Sch/U)_fppf ⟶ X` is smooth, and a finite type point `u0` of `U`
with residue field `k` such that `x|_{u0} ≅ x0`. -/
@[stacks 07XY]
theorem nonempty_smoothFiniteTypeObject {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [LimitPreserving X] [HasRimSchlessinger X]
    [HasFiniteDimensionalPredeformations X] [OpennessOfVersality X]
    (h_diag :
      relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (h_eff : ∀ ξ : FormalObject X, FormalObject.IsEffective ξ)
    {k : Type u} [Field k] (kToS : Spec (CommRingCat.of k) ⟶ S)
    [LocallyOfFiniteType kToS] (x0 : X.p.Fiber (Over.mk kToS)) (s : S)
    (hs : kToS (closedPoint k) = s) [IsGRing (S.presheaf.stalk s)] :
    Nonempty (SmoothFiniteTypeObject kToS x0) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
