module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.MultiplicativeGroup
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.GroupScheme.Action

@[expose] public section

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj ModObj
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineSpace

/-- Affine line over a field `k`. -/
abbrev affineLine (k : Type u) [Field k] : Scheme.{u} :=
  𝔸(ULift.{u} (Fin 1); Spec (.of k))

/-- Affine line over `Spec (.of k)`, as an object of the slice. -/
abbrev affineLineOver (k : Type u) [Field k] : Over (Spec (.of k)) :=
  Scheme.asOver (affineLine k) (Spec (.of k))

/-- The tautological global unit on `𝔾ₘ` over `Spec (.of k)`. -/
def scalingUnit (k : Type u) [Field k] : Γ((𝔾ₘ[Spec (.of k)]).X.left, ⊤) :=
  (MultiplicativeGroup.baseChangeHomEquiv (Spec (.of k)) (𝔾ₘ[Spec (.of k)]).X (𝟙 _)).val

/-- The tautological unit is the value of the relative points equivalence at `𝟙`. -/
theorem scalingUnit_spec (k : Type u) [Field k] :
    scalingUnit k =
      (MultiplicativeGroup.baseChangeHomEquiv (Spec (.of k)) (𝔾ₘ[Spec (.of k)]).X
        (𝟙 _)).val :=
  rfl

/-- Underlying scheme map of the usual `𝔾ₘ`-scaling action on the affine line. -/
def scalingHomLeft (k : Type u) [Field k] :
    ((𝔾ₘ[Spec (.of k)]).X ⊗ affineLineOver k).left ⟶ affineLine k :=
  homOfVector ((𝔾ₘ[Spec (.of k)]).X ⊗ affineLineOver k).hom fun i ↦
    (fst (𝔾ₘ[Spec (.of k)]).X (affineLineOver k)).left.appTop (scalingUnit k) *
      (snd (𝔾ₘ[Spec (.of k)]).X (affineLineOver k)).left.appTop (coord (Spec (.of k)) i)

/-- The usual multiplication action map `𝔾ₘ × 𝔸¹ ⟶ 𝔸¹` over a field. -/
def scalingHom (k : Type u) [Field k] :
    (𝔾ₘ[Spec (.of k)]).X ⊗ affineLineOver k ⟶ affineLineOver k :=
  Over.homMk (scalingHomLeft k) (homOfVector_over _ _)

/-- On coordinates, scaling multiplies the tautological `𝔾ₘ`-unit by the affine coordinate. -/
theorem scalingHom_spec (k : Type u) [Field k] (i : ULift.{u} (Fin 1)) :
    (scalingHom k).left.appTop (coord (Spec (.of k)) i) =
      (fst (𝔾ₘ[Spec (.of k)]).X (affineLineOver k)).left.appTop (scalingUnit k) *
        (snd (𝔾ₘ[Spec (.of k)]).X (affineLineOver k)).left.appTop
          (coord (Spec (.of k)) i) :=
  homOfVector_appTop_coord _ _ i

/-- The identity of the multiplicative group acts trivially on the affine line. -/
theorem scalingHom_one_smul (k : Type u) [Field k] :
    η ▷ affineLineOver k ≫ scalingHom k = (λ_ (affineLineOver k)).hom :=
  sorry

/-- Multiplication in the multiplicative group is compatible with scaling the affine line. -/
theorem scalingHom_mul_smul (k : Type u) [Field k] :
    (μ ▷ affineLineOver k) ≫ scalingHom k =
      (α_ (𝔾ₘ[Spec (.of k)]).X (𝔾ₘ[Spec (.of k)]).X (affineLineOver k)).hom ≫
        ((𝔾ₘ[Spec (.of k)]).X ◁ scalingHom k) ≫ scalingHom k :=
  sorry

/-- Module-object structure for the usual `𝔾ₘ`-scaling action on the affine line. -/
@[reducible]
def scalingModObj (k : Type u) [Field k] :
    ModObj (𝔾ₘ[Spec (.of k)]).X (affineLineOver k) where
  smul := scalingHom k
  one_smul := scalingHom_one_smul k
  mul_smul := scalingHom_mul_smul k

/-- The usual multiplication action of `𝔾ₘ` on the affine line over a field. -/
@[reducible]
def scalingAction (k : Type u) [Field k] :
    GroupScheme.Action (𝔾ₘ[Spec (.of k)]).toGrp where
  X := affineLineOver k
  mod := scalingModObj k

/-- The underlying object of `scalingAction` is the affine line over `k`. -/
theorem scalingAction_X (k : Type u) [Field k] :
    (scalingAction k).X = affineLineOver k :=
  rfl

/-- The stored action morphism of `scalingAction` is `scalingHom`. -/
theorem scalingAction_smul (k : Type u) [Field k] :
    (scalingAction k).mod.smul = scalingHom k :=
  rfl

end AlgebraicGeometry.AffineSpace

namespace AlgebraicGeometry

/-- Affine line over a field is algebraic. -/
instance instAlgebraic_affineLineOverField (k : Type u) [Field k] :
    Algebraic (AffineSpace.affineLineOver k) :=
  sorry

end AlgebraicGeometry
