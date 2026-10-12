/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_21_1_AdicSquare
public import stacks_project.Chap88.Definition_88_21_1_Formal
public import stacks_project.Chap88.Definition_88_21_1_Spf

/-!
# Rig-surjective morphisms of formal algebraic spaces

A locally of finite type morphism of locally Noetherian formal algebraic spaces
is rig-surjective when every adic test map from the formal spectrum of a complete
discrete valuation ring lifts after an extension of complete discrete valuation
rings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Definition 88.21.1: let `S` be a scheme, and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. Assume that `X` and `Y` are locally Noetherian
and that `f` is locally of finite type. We say `f` is rig-surjective if for every
solid diagram of an adic morphism `p : Spf(R) ⟶ Y` from a complete discrete
valuation ring `R` there exists an extension of complete discrete valuation rings
`R ⊂ R'` and a morphism `Spf(R') ⟶ X` making the displayed triangle commute. -/
@[stacks 0AQQ, mk_iff]
class RigSurjective {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f] : Prop where
  /-- Every solid adic `Spf` square admits an extension of complete discrete
  valuation rings together with a lift `Spf(R') ⟶ X`. -/
  exists_extension : ∀ sq : AdicSpfSquare f, Nonempty sq.Extension

namespace RigSurjective

/-- The identity morphism of a locally Noetherian formal algebraic space is
rig-surjective. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] : RigSurjective (𝟙 X) :=
  sorry

/-- A locally of finite type morphism of locally Noetherian formal algebraic
spaces is rig-surjective if and only if every adic complete-DVR test map lifts
after an extension of complete discrete valuation rings. -/
theorem spec {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    RigSurjective f ↔ ∀ sq : AdicSpfSquare f, Nonempty sq.Extension :=
  sorry

end RigSurjective

end AlgebraicGeometry.FormalAlgebraicSpace
