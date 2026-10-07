module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.RingTheory.Regular.GRing
public import stacks_project.Chap03.Lemma_3_9_4_Size
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.Definition_98_5_1
public import stacks_project.Chap98.Definition_98_9_4_Effective
public import stacks_project.Chap98.Definition_98_13_1_Openness
public import stacks_project.Chap98.Lemma_98_13_8_Predeformations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Algebraic spaces from Artin's axioms

A set-valued functor on schemes over a locally Noetherian base whose diagonal is
representable by algebraic spaces, and which satisfies the functorial Artin
axioms of Section 98.15 together with G-ring stalks at finite type points, is an
algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Over

/-- The category fibred in groupoids associated to a set-valued functor on
schemes over `S`, obtained by the discrete Grothendieck construction and
forgetting from sets to groupoids. -/
abbrev toGroupoidsOver {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    GroupoidsOver S :=
  (Sets.toGroupoids (Over S)).obj ((Sets.ofPresheaf (Over S)).obj F)

/-- `toGroupoidsOver F` is the discrete Grothendieck construction of `F`,
forgotten to groupoids. -/
theorem toGroupoidsOver_eq {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    toGroupoidsOver F =
      (Sets.toGroupoids (Over S)).obj ((Sets.ofPresheaf (Over S)).obj F) :=
  sorry

/-- The projection of `toGroupoidsOver F` is the opposite category-of-elements
projection of `F`. -/
theorem toGroupoidsOver_p {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    (toGroupoidsOver F).p = ((Sets.ofPresheaf (Over S)).obj F).p :=
  sorry

/-- Artin axiom [-1]: the values of `F` on spectra of finite-type fields over
`S` are bounded by the Stacks size of some scheme over `S`. -/
def boundedOnFiniteTypeFields {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    Prop :=
  ∃ U : Over S, ∀ (k : Type u) [Field k] (f : Spec (CommRingCat.of k) ⟶ S)
    [LocallyOfFiniteType f],
      Cardinal.mk (F.obj (op (Over.mk f))) ≤ U.left.size

/-- Axiom [-1] unfolds to a comparison of `F.obj` cardinalities against
`Scheme.size`. -/
theorem boundedOnFiniteTypeFields_iff {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type u) :
    boundedOnFiniteTypeFields F ↔
      ∃ U : Over S, ∀ (k : Type u) [Field k]
        (f : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType f],
          Cardinal.mk (F.obj (op (Over.mk f))) ≤ U.left.size :=
  sorry

end AlgebraicGeometry.Scheme.Over

namespace AlgebraicGeometry.AlgebraicSpace

open Scheme.Over

/-- Proposition 98.16.1: let `S` be a locally Noetherian scheme and let
`F : (Over S)ᵒᵖ ⥤ Type u`. Assume the diagonal `diag F` is representable by
algebraic spaces, `F` satisfies axioms [-1] (`boundedOnFiniteTypeFields`),
[0] (`Presheaf.IsSheaf` for `Scheme.etaleTopology.over S`), [1]
(`PreservesDirectedAffineLimits`), [2]–[5] on `toGroupoidsOver F`
(`GroupoidsOver.HasRimSchlessinger`, `HasFiniteDimensionalPredeformations`,
effectiveness of formal objects, and `OpennessOfVersality`), and
`S.presheaf.stalk s` is a G-ring for every finite type point `s` of `S`. Then
`F` is an algebraic space. -/
@[stacks 07Y1]
theorem IsAlgebraicSpace.of_artinAxioms {S : Scheme.{u}} [IsLocallyNoetherian S]
    {F : (Over S)ᵒᵖ ⥤ Type u} (hΔ : representableByAlgebraicSpaces (diag F))
    (h_size : boundedOnFiniteTypeFields F)
    (h0 : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (h1 : PreservesDirectedAffineLimits S F)
    (hRS : GroupoidsOver.HasRimSchlessinger (toGroupoidsOver F))
    (hT : GroupoidsOver.HasFiniteDimensionalPredeformations (toGroupoidsOver F))
    (h_eff : ∀ ξ : GroupoidsOver.FormalObject (toGroupoidsOver F),
      GroupoidsOver.FormalObject.IsEffective ξ)
    (h_open : GroupoidsOver.OpennessOfVersality (toGroupoidsOver F))
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    IsAlgebraicSpace F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
