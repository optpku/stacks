module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.MultiplicativeGroup
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import stacks_project.Chap100.Definition_100_12_3_Dimension
public import stacks_project.Chap100.Example_100_12_5_Quotient

/-!
# Scaling action of 𝔾ₘ on the affine line

The usual multiplication action of the multiplicative group on the affine line over a
field, the quotient stack `[𝔸¹ / 𝔾ₘ]`, and the two orbit points of that quotient.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj ModObj
open scoped AlgebraicGeometry Bicategory

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
  sorry

/-- Underlying scheme map of the usual `𝔾ₘ`-scaling action on the affine line. -/
def scalingHomLeft (k : Type u) [Field k] :
    ((𝔾ₘ[Spec (.of k)]).X ⊗ affineLineOver k).left ⟶ affineLine k :=
  homOfVector ((𝔾ₘ[Spec (.of k)]).X ⊗ affineLineOver k).hom fun i ↦
    (fst (𝔾ₘ[Spec (.of k)]).X (affineLineOver k)).left.appTop (scalingUnit k) *
      (snd (𝔾ₘ[Spec (.of k)]).X (affineLineOver k)).left.appTop (coord (Spec (.of k)) i)

/-- Scaling on the affine line is a morphism over `Spec (.of k)`. -/
theorem scalingHom_w (k : Type u) [Field k] :
    scalingHomLeft k ≫ affineLine k ↘ Spec (.of k) =
      ((𝔾ₘ[Spec (.of k)]).X ⊗ affineLineOver k).hom :=
  sorry

/-- The usual multiplication action map `𝔾ₘ × 𝔸¹ ⟶ 𝔸¹` over a field. -/
def scalingHom (k : Type u) [Field k] :
    (𝔾ₘ[Spec (.of k)]).X ⊗ affineLineOver k ⟶ affineLineOver k :=
  Over.homMk (scalingHomLeft k) (scalingHom_w k)

/-- On coordinates, scaling multiplies the tautological `𝔾ₘ`-unit by the affine coordinate. -/
theorem scalingHom_spec (k : Type u) [Field k] (i : ULift.{u} (Fin 1)) :
    (scalingHom k).left.appTop (coord (Spec (.of k)) i) =
      (fst (𝔾ₘ[Spec (.of k)]).X (affineLineOver k)).left.appTop (scalingUnit k) *
        (snd (𝔾ₘ[Spec (.of k)]).X (affineLineOver k)).left.appTop
          (coord (Spec (.of k)) i) :=
  sorry

/-- Module-object structure for the usual `𝔾ₘ`-scaling action on the affine line. -/
@[reducible]
def scalingModObj (k : Type u) [Field k] :
    ModObj (𝔾ₘ[Spec (.of k)]).X (affineLineOver k) where
  smul := scalingHom k
  one_smul := sorry
  mul_smul := sorry

/-- The usual multiplication action of `𝔾ₘ` on the affine line over a field. -/
def scalingAction (k : Type u) [Field k] :
    GroupScheme.Action (𝔾ₘ[Spec (.of k)]).toGrp where
  X := affineLineOver k
  mod := scalingModObj k

/-- The underlying object of `scalingAction` is the affine line over `k`. -/
theorem scalingAction_X (k : Type u) [Field k] :
    (scalingAction k).X = affineLineOver k :=
  sorry

/-- The stored action morphism of `scalingAction` is `scalingHom`. -/
theorem scalingAction_smul (k : Type u) [Field k] :
    (scalingAction k).mod.smul = scalingHom k :=
  sorry

end AlgebraicGeometry.AffineSpace

namespace AlgebraicGeometry

/-- Affine line over a field is algebraic. -/
instance instAlgebraic_affineLineOverField (k : Type u) [Field k] :
    Algebraic (AffineSpace.affineLineOver k) :=
  sorry

/-- The multiplicative group over a field is algebraic. -/
instance instAlgebraic_multiplicativeGroupOverField (k : Type u) [Field k] :
    Algebraic (𝔾ₘ[Spec (.of k)]).toGrp.X :=
  sorry

/-- The usual scaling action is algebraic on its underlying object. -/
instance instAlgebraic_scalingAction (k : Type u) [Field k] :
    Algebraic (AffineSpace.scalingAction k).X :=
  instAlgebraic_affineLineOverField k

end AlgebraicGeometry

namespace AlgebraicGeometry.AlgebraicStack

/-- The quotient stack `[𝔸¹ / 𝔾ₘ]` for the usual scaling action over a field. -/
def affineLineQuotient (k : Type u) [Field k] : GroupoidsOver (Spec (.of k)) :=
  quotient (𝔾ₘ[Spec (.of k)]).toGrp (AffineSpace.scalingAction k)

/-- `affineLineQuotient` is the quotient stack of the usual scaling action. -/
theorem affineLineQuotient_spec (k : Type u) [Field k] :
    affineLineQuotient k = quotient (𝔾ₘ[Spec (.of k)]).toGrp (AffineSpace.scalingAction k) :=
  sorry

/-- The scaling quotient stack is an algebraic stack. -/
instance instAlgebraicStack_affineLineQuotient (k : Type u) [Field k] :
    AlgebraicStack (affineLineQuotient k) :=
  instAlgebraicStack_quotient (𝔾ₘ[Spec (.of k)]).toGrp (AffineSpace.scalingAction k)

/-- The scaling quotient stack is locally Noetherian. -/
instance instIsLocallyNoetherian_affineLineQuotient (k : Type u) [Field k] :
    IsLocallyNoetherian (affineLineQuotient k) :=
  instIsLocallyNoetherian_quotient (𝔾ₘ[Spec (.of k)]).toGrp (AffineSpace.scalingAction k)

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.AlgebraicStack.AffineLineQuotient

open AffineSpace GroupoidAlgebraicSpace GroupoidScheme

/-- The atlas `𝔸¹ ⟶ [𝔸¹ / 𝔾ₘ]` of the scaling quotient stack. -/
def atlas (k : Type u) [Field k] :
    GroupoidsOver.slice (affineLineOver k) ⟶ affineLineQuotient k :=
  (AlgebraicSpace.ofOverSliceEquiv (scalingAction k).X).inv ≫
    (ofGroupoidScheme (ofAction (𝔾ₘ[Spec (.of k)]).toGrp (scalingAction k))).atlas

/-- The origin of the affine line over `k`, as a scheme point. -/
def origin (k : Type u) [Field k] : affineLine k :=
  homOfVector (𝟙 (Spec (.of k))) (fun _ ↦ 0) (default : Spec (.of k))

/-- The unit section of the affine line over `k`, as a scheme point. -/
def unitSection (k : Type u) [Field k] : affineLine k :=
  homOfVector (𝟙 (Spec (.of k))) (fun _ ↦ 1) (default : Spec (.of k))

/-- The closed point of `[𝔸¹ / 𝔾ₘ]`, the atlas image of the origin of `𝔸¹`. -/
def closedPoint (k : Type u) [Field k] : Points (affineLineQuotient k) :=
  Points.mapSlice (atlas k) (origin k)

/-- The generic point of `[𝔸¹ / 𝔾ₘ]`, the atlas image of the unit section of `𝔸¹`. -/
def genericPoint (k : Type u) [Field k] : Points (affineLineQuotient k) :=
  Points.mapSlice (atlas k) (unitSection k)

/-- `closedPoint` is the image of the origin along the quotient atlas. -/
theorem closedPoint_spec (k : Type u) [Field k] :
    closedPoint k = Points.mapSlice (atlas k) (origin k) :=
  sorry

/-- `genericPoint` is the image of the unit section along the quotient atlas. -/
theorem genericPoint_spec (k : Type u) [Field k] :
    genericPoint k = Points.mapSlice (atlas k) (unitSection k) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.AffineLineQuotient

