/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Lemma_94_14_3_Pullback
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat
public import stacks_project.Chap101.Definition_101_4_1_Separation

/-!
# Locally quasi-finite flat algebraic-space covers of algebraic stacks

A morphism of algebraic stacks is quasi-DM precisely when 2-fibre products
against algebraic spaces admit a surjective, flat, locally of finite
presentation, locally quasi-finite morphism from an algebraic space. This
module records the covering predicates; the source-facing equivalences live
in the labeled item file.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- There exists an algebraic space `W` over `S` and a surjective, flat,
locally of finite presentation, locally quasi-finite morphism
`W.toGroupoids ⟶ X`. -/
def existsLocallyQuasiFiniteFlatSpaceCover {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] : Prop :=
  ∃ (W : AlgebraicSpace S) (h : W.toGroupoids ⟶ X),
    Groupoids.Hom.Surjective h ∧ Groupoids.Hom.Flat h ∧
      Groupoids.Hom.LocallyOfFinitePresentation h ∧
      Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) h

namespace existsLocallyQuasiFiniteFlatSpaceCover

/-- `existsLocallyQuasiFiniteFlatSpaceCover X` unpacks to a surjective, flat,
locally of finite presentation, locally quasi-finite morphism from an
algebraic space over `S`. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    existsLocallyQuasiFiniteFlatSpaceCover X ↔
      ∃ (W : AlgebraicSpace S) (h : W.toGroupoids ⟶ X),
        Groupoids.Hom.Surjective h ∧ Groupoids.Hom.Flat h ∧
          Groupoids.Hom.LocallyOfFinitePresentation h ∧
          Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) h :=
  sorry

/-- A surjective, flat, locally of finite presentation, locally quasi-finite
morphism from an algebraic space over `S` witnesses
`existsLocallyQuasiFiniteFlatSpaceCover`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {W : AlgebraicSpace S} (h : W.toGroupoids ⟶ X)
    [Groupoids.Hom.Surjective h] [Groupoids.Hom.Flat h]
    [Groupoids.Hom.LocallyOfFinitePresentation h]
    (h_locallyQuasiFinite :
      Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) h) :
    existsLocallyQuasiFiniteFlatSpaceCover X :=
  sorry

/-- `existsLocallyQuasiFiniteFlatSpaceCover X` supplies a surjective, flat,
locally of finite presentation, locally quasi-finite morphism from an
algebraic space over `S`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (hX : existsLocallyQuasiFiniteFlatSpaceCover X) :
    ∃ (W : AlgebraicSpace S) (h : W.toGroupoids ⟶ X),
      Groupoids.Hom.Surjective h ∧ Groupoids.Hom.Flat h ∧
        Groupoids.Hom.LocallyOfFinitePresentation h ∧
        Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) h :=
  sorry

end existsLocallyQuasiFiniteFlatSpaceCover

namespace QuasiDM

/-- For every algebraic space `V` and morphism `g : V.toGroupoids ⟶ Y`, the
2-fibre product `TwoFibreProduct.apex f g` (informally `X ×_Y V`) admits a
surjective, flat, locally of finite presentation, locally quasi-finite
morphism from an algebraic space. -/
def existsCoverOnPullbacks {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y),
    existsLocallyQuasiFiniteFlatSpaceCover
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)

/-- `existsCoverOnPullbacks f` unpacks to a locally quasi-finite flat
algebraic-space cover of every 2-fibre product of `f` against an algebraic
space over the target. -/
theorem existsCoverOnPullbacks.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    existsCoverOnPullbacks f ↔
      ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y),
        existsLocallyQuasiFiniteFlatSpaceCover
          (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) :=
  sorry

namespace existsCoverOnPullbacks

/-- A locally quasi-finite flat algebraic-space cover of every 2-fibre product
of `f` against an algebraic space over the target witnesses
`existsCoverOnPullbacks`. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h : ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y),
      existsLocallyQuasiFiniteFlatSpaceCover
        (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)) :
    existsCoverOnPullbacks f :=
  sorry

/-- Under `existsCoverOnPullbacks f`, every 2-fibre product of `f` against an
algebraic space over the target admits a locally quasi-finite flat
algebraic-space cover. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : existsCoverOnPullbacks f) (V : AlgebraicSpace S)
    (g : V.toGroupoids ⟶ Y) :
    existsLocallyQuasiFiniteFlatSpaceCover
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) :=
  sorry

end existsCoverOnPullbacks

/-- There exist algebraic spaces `U`, `V` and a surjective, flat, locally of
finite presentation morphism `g : V.toGroupoids ⟶ Y` such that
`TwoFibreProduct.apex f g` (informally `X ×_Y V`) admits a surjective, flat,
locally of finite presentation, locally quasi-finite morphism from `U`. -/
def existsCoverOverFppf {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∃ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y),
    Groupoids.Hom.Surjective g ∧ Groupoids.Hom.Flat g ∧
      Groupoids.Hom.LocallyOfFinitePresentation g ∧
      existsLocallyQuasiFiniteFlatSpaceCover
        (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)

/-- `existsCoverOverFppf f` unpacks to one fppf algebraic-space cover of the
target together with a locally quasi-finite flat algebraic-space cover of the
corresponding 2-fibre product. -/
theorem existsCoverOverFppf.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    existsCoverOverFppf f ↔
      ∃ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y),
        Groupoids.Hom.Surjective g ∧ Groupoids.Hom.Flat g ∧
          Groupoids.Hom.LocallyOfFinitePresentation g ∧
          existsLocallyQuasiFiniteFlatSpaceCover
            (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) :=
  sorry

namespace existsCoverOverFppf

/-- An fppf algebraic-space cover of the target together with a locally
quasi-finite flat algebraic-space cover of the 2-fibre product witnesses
`existsCoverOverFppf`. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {V : AlgebraicSpace S} (g : V.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (h : existsLocallyQuasiFiniteFlatSpaceCover
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)) :
    existsCoverOverFppf f :=
  sorry

/-- `existsCoverOverFppf f` supplies an fppf algebraic-space cover of the
target and a locally quasi-finite flat algebraic-space cover of the
corresponding 2-fibre product. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : existsCoverOverFppf f) :
    ∃ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y),
      Groupoids.Hom.Surjective g ∧ Groupoids.Hom.Flat g ∧
        Groupoids.Hom.LocallyOfFinitePresentation g ∧
        existsLocallyQuasiFiniteFlatSpaceCover
          (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) :=
  sorry

end existsCoverOverFppf

/-- The covering criterion on every algebraic-space test implies the existence
of one fppf algebraic-space cover of the target with a locally quasi-finite
flat algebraic-space cover of the 2-fibre product. -/
theorem existsCoverOverFppf_of_existsCoverOnPullbacks {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h : existsCoverOnPullbacks f) : existsCoverOverFppf f :=
  sorry

end QuasiDM

end AlgebraicGeometry.AlgebraicStack
