module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.RingTheory.Regular.GRing
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap98.Proposition_98_16_1
import Mathlib.Tactic.CrossRefAttribute

/-!
# Algebraic spaces from a monomorphism into a locally finite type algebraic space

If `S` is locally Noetherian, `a : F ⟶ G.functorOfPoints` is a monomorphism of
set-valued functors on schemes over `S`, `F` satisfies the functorial Artin
axioms [0], [1], [2], [4], and [5], stalks `S.presheaf.stalk s` are G-rings at
finite type points, and `G` is an algebraic space locally of finite type over
`S`, then `F` is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open Scheme.Over

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 98.16.2: let `S` be a locally Noetherian scheme and let
`a : F ⟶ G.functorOfPoints` be a transformation of functors
`(Over S)ᵒᵖ ⥤ Type u`. Assume `a` is injective (`Mono a`), `F` satisfies
axioms [0] (`Presheaf.IsSheaf` for `Scheme.etaleTopology.over S`), [1]
(`PreservesDirectedAffineLimits`), [2], [4], and [5] on `toGroupoidsOver F`
(`GroupoidsOver.HasRimSchlessinger`, effectiveness of formal objects, and
`OpennessOfVersality`), `S.presheaf.stalk s` is a G-ring for every finite type
point `s` of `S`, and `G` is an algebraic space locally of finite type over
`S` (`LocallyOfFiniteType (toBase G)`). Then `F` is an algebraic space. -/
@[stacks 07Y2]
theorem IsAlgebraicSpace.of_mono {S : Scheme.{u}} [IsLocallyNoetherian S]
    {F : (Over S)ᵒᵖ ⥤ Type u} {G : AlgebraicSpace S}
    (a : F ⟶ G.functorOfPoints) [Mono a] [LocallyOfFiniteType (toBase G)]
    (h0 : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (h1 : PreservesDirectedAffineLimits S F)
    (hRS : GroupoidsOver.HasRimSchlessinger (toGroupoidsOver F))
    (h_eff : ∀ ξ : GroupoidsOver.FormalObject (toGroupoidsOver F),
      GroupoidsOver.FormalObject.IsEffective ξ)
    (h_open : GroupoidsOver.OpennessOfVersality (toGroupoidsOver F))
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    IsAlgebraicSpace F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
