module

public import stacks_project.Chap70.Situation_70_5_5_QcqsAffine
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Lemma_94_14_3_Pullback
public import stacks_project.Chap100.Definition_100_6_1_QuasiCompact
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_8_1_Noetherian

/-!
# Eventual separatedness of stack base change along a directed affine limit

If a morphism from a quasi-compact quasi-separated algebraic stack to a
distinguished stage of a directed inverse system of qcqs algebraic spaces with
affine transitions becomes separated after base change to the limit, then the
base changes to all sufficiently late stages are separated.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
variable [∀ i, AlgebraicSpace.IsQuasiCompact (D.obj i)]
variable [∀ i, AlgebraicSpace.IsQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), AlgebraicSpace.Affine (D.map (homOfLE h))]

/-- The 2-fibre product `Y ×_{Y0} 𝒳0` of a morphism of algebraic stacks to the
distinguished stage with the limit projection `Y ⟶ Y0`. -/
abbrev pullbackAlongLimit {s : AlgebraicSpace.Limit.QcqsAffineLimit D} {X0 : GroupoidsOver S}
    (f : X0 ⟶ (D.obj s.base).toGroupoids) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} f
    (AlgebraicSpace.toGroupoids.map (s.limitCone.cone.π.app s.base))

/-- The projection `Y ×_{Y0} 𝒳0 ⟶ Y`. -/
abbrev pullbackAlongLimit.snd {s : AlgebraicSpace.Limit.QcqsAffineLimit D} {X0 : GroupoidsOver S}
    (f : X0 ⟶ (D.obj s.base).toGroupoids) :
    pullbackAlongLimit f ⟶ s.limitCone.cone.pt.toGroupoids :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u} f
    (AlgebraicSpace.toGroupoids.map (s.limitCone.cone.π.app s.base))

/-- The projection `Y ×_{Y0} 𝒳0 ⟶ Y` is the second 2-fibre-product projection
along the limit map to the distinguished stage. -/
theorem pullbackAlongLimit.snd_eq {s : AlgebraicSpace.Limit.QcqsAffineLimit D} {X0 : GroupoidsOver S}
    (f : X0 ⟶ (D.obj s.base).toGroupoids) :
    pullbackAlongLimit.snd f =
      TwoFibreProduct.snd.{u + 1, u, u + 1, u} f
        (AlgebraicSpace.toGroupoids.map (s.limitCone.cone.π.app s.base)) :=
  sorry

/-- The 2-fibre product `Yi ×_{Y0} 𝒳0` of a morphism of algebraic stacks to the
distinguished stage with the stage map `Yi ⟶ Y0`. -/
abbrev pullbackAlongStage {s : AlgebraicSpace.Limit.QcqsAffineLimit D} {X0 : GroupoidsOver S}
    (f : X0 ⟶ (D.obj s.base).toGroupoids) (i : I) (hi : s.base ≤ i) :
    GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} f
    (AlgebraicSpace.toGroupoids.map (D.map (homOfLE hi)))

/-- The projection `Yi ×_{Y0} 𝒳0 ⟶ Yi`. -/
abbrev pullbackAlongStage.snd {s : AlgebraicSpace.Limit.QcqsAffineLimit D} {X0 : GroupoidsOver S}
    (f : X0 ⟶ (D.obj s.base).toGroupoids) (i : I) (hi : s.base ≤ i) :
    pullbackAlongStage f i hi ⟶ (D.obj i).toGroupoids :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u} f
    (AlgebraicSpace.toGroupoids.map (D.map (homOfLE hi)))

/-- The projection `Yi ×_{Y0} 𝒳0 ⟶ Yi` is the second 2-fibre-product projection
along the stage map to the distinguished stage. -/
theorem pullbackAlongStage.snd_eq {s : AlgebraicSpace.Limit.QcqsAffineLimit D} {X0 : GroupoidsOver S}
    (f : X0 ⟶ (D.obj s.base).toGroupoids) (i : I) (hi : s.base ≤ i) :
    pullbackAlongStage.snd f i hi =
      TwoFibreProduct.snd.{u + 1, u, u + 1, u} f
        (AlgebraicSpace.toGroupoids.map (D.map (homOfLE hi))) :=
  sorry

/-- Lemma 102.4.2: In Situation 102.4.1, packaged as `AlgebraicSpace.Limit.QcqsAffineLimit D`, if
`f : 𝒳0 ⟶ Y0` is a morphism from a quasi-compact quasi-separated algebraic
stack to the distinguished stage and the limit base change
`Y ×_{Y0} 𝒳0 ⟶ Y` is separated, then `Yi ×_{Y0} 𝒳0 ⟶ Yi` is separated for
every sufficiently large `i`.

Here `D.obj i` is the stage `Yi`, `s.base` is the distinguished index `0`,
`s.limitCone.cone.pt` is the limit `Y`, and the base-change morphisms are the
second 2-fibre-product projections `TwoFibreProduct.snd`. -/
@[stacks 0CPZ]
theorem exists_eventually_separated_stage (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    {X0 : GroupoidsOver S} [AlgebraicStack X0] [IsQuasiCompact X0]
    [IsQuasiSeparated X0] (f : X0 ⟶ (D.obj s.base).toGroupoids)
    (hY : Separated (pullbackAlongLimit.snd f)) :
    ∃ (i : I) (hi : s.base ≤ i),
      ∀ (j : I) (hj : i ≤ j),
        Separated (pullbackAlongStage.snd f j (hi.trans hj)) :=
  sorry

/-- If the limit base change is separated, then the base change to some stage
above the distinguished index is separated. -/
theorem exists_separated_stage (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    {X0 : GroupoidsOver S} [AlgebraicStack X0] [IsQuasiCompact X0]
    [IsQuasiSeparated X0] (f : X0 ⟶ (D.obj s.base).toGroupoids)
    (hY : Separated (pullbackAlongLimit.snd f)) :
    ∃ (i : I) (hi : s.base ≤ i), Separated (pullbackAlongStage.snd f i hi) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
