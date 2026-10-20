module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.AbsolutelyQcqs
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiSeparated

/-!
# Eventual separatedness along directed affine limits

A morphism from a quasi-compact quasi-separated algebraic stack to a stage of
a directed inverse system of quasi-compact, absolutely quasi-separated algebraic
spaces with affine transitions is separated at every sufficiently late stage
if its base change to the specified limit is separated.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
variable [∀ i, AlgebraicSpace.IsQuasiCompact (D.obj i)]
variable [∀ i, AlgebraicSpace.IsAbsolutelyQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), AlgebraicSpace.Affine (D.map (homOfLE h))]

/-- The 2-fibre product of a groupoid fibration over the distinguished stage
with the specified limit projection to that stage. -/
abbrev pullbackAlongLimit (s : AlgebraicSpace.Limit.AbsolutelyQcqsAffineLimit D)
    {X0 : GroupoidsOver S} (f : X0 ⟶ (D.obj s.base).toGroupoids) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} f
    (AlgebraicSpace.toGroupoids.map (s.limitCone.cone.π.app s.base))

/-- The second projection from the base change to the specified limit. -/
abbrev pullbackAlongLimit.snd (s : AlgebraicSpace.Limit.AbsolutelyQcqsAffineLimit D)
    {X0 : GroupoidsOver S} (f : X0 ⟶ (D.obj s.base).toGroupoids) :
    pullbackAlongLimit s f ⟶ s.limitCone.cone.pt.toGroupoids :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u} f
    (AlgebraicSpace.toGroupoids.map (s.limitCone.cone.π.app s.base))

/-- The projection from the limit base change is the canonical second
2-fibre-product projection along the limit map to the distinguished stage. -/
theorem pullbackAlongLimit.snd_eq (s : AlgebraicSpace.Limit.AbsolutelyQcqsAffineLimit D)
    {X0 : GroupoidsOver S} (f : X0 ⟶ (D.obj s.base).toGroupoids) :
    pullbackAlongLimit.snd s f =
      TwoFibreProduct.snd.{u + 1, u, u + 1, u} f
        (AlgebraicSpace.toGroupoids.map (s.limitCone.cone.π.app s.base)) :=
  rfl

/-- The 2-fibre product of a groupoid fibration over the distinguished stage
with a transition map from a later stage. -/
abbrev pullbackAlongStage (s : AlgebraicSpace.Limit.AbsolutelyQcqsAffineLimit D)
    {X0 : GroupoidsOver S} (f : X0 ⟶ (D.obj s.base).toGroupoids)
    (i : I) (hi : s.base ≤ i) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} f
    (AlgebraicSpace.toGroupoids.map (D.map (homOfLE hi)))

/-- The second projection from the base change to a later stage. -/
abbrev pullbackAlongStage.snd (s : AlgebraicSpace.Limit.AbsolutelyQcqsAffineLimit D)
    {X0 : GroupoidsOver S} (f : X0 ⟶ (D.obj s.base).toGroupoids)
    (i : I) (hi : s.base ≤ i) :
    pullbackAlongStage s f i hi ⟶ (D.obj i).toGroupoids :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u} f
    (AlgebraicSpace.toGroupoids.map (D.map (homOfLE hi)))

/-- The projection from a stage base change is the canonical second
2-fibre-product projection along the transition to the distinguished stage. -/
theorem pullbackAlongStage.snd_eq (s : AlgebraicSpace.Limit.AbsolutelyQcqsAffineLimit D)
    {X0 : GroupoidsOver S} (f : X0 ⟶ (D.obj s.base).toGroupoids)
    (i : I) (hi : s.base ≤ i) :
    pullbackAlongStage.snd s f i hi =
      TwoFibreProduct.snd.{u + 1, u, u + 1, u} f
        (AlgebraicSpace.toGroupoids.map (D.map (homOfLE hi))) :=
  rfl

/-- If a morphism from a quasi-compact quasi-separated algebraic stack to the
distinguished stage becomes separated after base change to the specified
directed affine limit, its base changes to all sufficiently late stages are
separated. -/
theorem exists_eventually_separated_stage (s : AlgebraicSpace.Limit.AbsolutelyQcqsAffineLimit D)
    {X0 : GroupoidsOver S} [AlgebraicStack X0] [IsQuasiCompact X0]
    [IsQuasiSeparated X0] (f : X0 ⟶ (D.obj s.base).toGroupoids)
    (hY : Separated (pullbackAlongLimit.snd s f)) :
    ∃ (i : I) (hi : s.base ≤ i),
      ∀ (j : I) (hj : i ≤ j),
        Separated (pullbackAlongStage.snd s f j (hi.trans hj)) :=
  sorry

/-- If the limit base change is separated, then the base change to some stage
above the distinguished index is separated. -/
theorem exists_separated_stage (s : AlgebraicSpace.Limit.AbsolutelyQcqsAffineLimit D)
    {X0 : GroupoidsOver S} [AlgebraicStack X0] [IsQuasiCompact X0]
    [IsQuasiSeparated X0] (f : X0 ⟶ (D.obj s.base).toGroupoids)
    (hY : Separated (pullbackAlongLimit.snd s f)) :
    ∃ (i : I) (hi : s.base ≤ i), Separated (pullbackAlongStage.snd s f i hi) := by
  obtain ⟨i, hi, h⟩ := exists_eventually_separated_stage s f hY
  exact ⟨i, hi, h i le_rfl⟩

end AlgebraicGeometry.AlgebraicStack
