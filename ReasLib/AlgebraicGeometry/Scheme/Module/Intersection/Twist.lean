module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower.Multi

/-!
# Twists on closed subschemes

This leaf owns the tensor twists of a family of invertible modules after
pullback to a closed subscheme, together with their Euler characteristic over
a proper field base.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Intersection

/-- The exponent of the multilinear monomial `∏ j : Fin d, X_j`. -/
def multilinearExponent (d : ℕ) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ ↦ 1)

/-- The `{0, 1}`-valued exponent vector associated to a subset of the factors. -/
def subsetExponent {d : ℕ} (s : Finset (Fin d)) : Fin d → ℤ :=
  fun j ↦ if j ∈ s then 1 else 0

/-- The family obtained by pulling back all but the first factor of a nonempty finite family to a
closed subscheme. -/
noncomputable abbrev tailPullback
    {X : Scheme.{u}} {d : ℕ} (hd : 0 < d) (Z : X.IdealSheafData)
    (L : Fin d → X.Modules) : Fin (d - 1) → Z.subscheme.Modules :=
  fun i ↦
    (Scheme.Modules.pullback Z.subschemeι).obj
      (L (Fin.cast (Nat.succ_pred_eq_of_pos hd) i.succ))

/-- If every member of a finite family is invertible, then every member of its pulled-back tail
is invertible. -/
@[instance] theorem tailPullback_invertible
    {X : Scheme.{u}} {d : ℕ} (hd : 0 < d) (Z : X.IdealSheafData)
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)] :
    ∀ j : Fin (d - 1), Invertible (tailPullback hd Z L j) := sorry

/-- The pullback to a closed subscheme of one integral tensor power in a family of invertible
scheme modules. -/
noncomputable def pullbackTensorPower
    {X : Scheme.{u}} (Z : X.IdealSheafData)
    {d : ℕ} (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)]
    (n : Fin d → ℤ) (j : Fin d) : Z.subscheme.Modules :=
  (Scheme.Modules.pullback Z.subschemeι).obj (tensorPowerInt (L j) (n j))

/-- The ordered tensor twist on a closed subscheme formed from a family of pulled-back integral
tensor powers. -/
noncomputable def pullbackTensorTwist
    {X : Scheme.{u}} (Z : X.IdealSheafData)
    {d : ℕ} (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)]
    (n : Fin d → ℤ) : Z.subscheme.Modules :=
  (List.finRange d).foldr
    (fun j acc ↦ tensorObj (pullbackTensorPower Z L n j) acc)
    (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules)

/-- The closed-subscheme tensor twist unfolds to the ordered finite tensor product of its
pulled-back powers. -/
theorem pullbackTensorTwist_def
    {X : Scheme.{u}} (Z : X.IdealSheafData)
    {d : ℕ} (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)]
    (n : Fin d → ℤ) :
    pullbackTensorTwist Z L n =
      (List.finRange d).foldr
        (fun j acc ↦ tensorObj (pullbackTensorPower Z L n j) acc)
        (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules) := sorry

/-- The concrete pullback tensor twist of invertible modules is coherent. -/
@[instance] theorem pullbackTensorTwist_isCoherent
    {X : Scheme.{u}} (Z : X.IdealSheafData)
    [IsLocallyNoetherian Z.subscheme]
    {d : ℕ} (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)]
    (n : Fin d → ℤ) :
    (pullbackTensorTwist Z L n).IsCoherent := sorry

/-- The ordered ambient tensor twist beginning with the pushforward of the structure module of a
closed subscheme and followed by integral powers of invertible modules. -/
noncomputable def closedImmersionStructureTwist
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    {Y : Scheme.{u}} (inclusion : Y ⟶ X) [IsClosedImmersion inclusion]
    {d : ℕ}
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)]
    (n : Fin d → ℤ) : X.Modules :=
  Scheme.Modules.TensorPower.multiTwist
    ((Scheme.Modules.pushforward inclusion).obj
      (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) L n

/-- The ambient tensor twist associated to an effective-Cartier ideal-sheaf presentation. -/
noncomputable abbrev pushforwardStructureTwist
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData) {d : ℕ}
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)]
    (n : Fin d → ℤ) : X.Modules :=
  closedImmersionStructureTwist k f Z.subschemeι L n

/-- The ambient pushforward structure twist unfolds to its ordered finite tensor product. -/
theorem pushforwardStructureTwist_def
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData) {d : ℕ}
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)]
    (n : Fin d → ℤ) :
    pushforwardStructureTwist k f Z L n =
      (List.finRange d).foldl
        (fun acc j ↦ tensorObj acc (tensorPowerInt (L j) (n j)))
        ((Scheme.Modules.pushforward Z.subschemeι).obj
          (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules)) := sorry

/-- The ambient pushforward structure twist on a scheme proper over a field is coherent. -/
instance closedImmersionStructureTwist_isCoherent
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    {Y : Scheme.{u}} (inclusion : Y ⟶ X) [IsClosedImmersion inclusion]
    {d : ℕ}
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)]
    (n : Fin d → ℤ) :
    (closedImmersionStructureTwist k f inclusion L n).IsCoherent := sorry

/-- The Euler characteristic of the pullback tensor twist on a closed subscheme of a scheme
proper over a field. -/
noncomputable def eulerCharacteristic
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData) {d : ℕ}
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)]
    (n : Fin d → ℤ) : ℤ :=
  @Scheme.Hom.eulerCharacteristic k _ Z.subscheme
    (Z.subschemeι ≫ f) inferInstance (pullbackTensorTwist Z L n)
    (@pullbackTensorTwist_isCoherent X Z
      (LocallyOfFiniteType.isLocallyNoetherian (Z.subschemeι ≫ f)) d L _ n)

/-- The closed-subscheme twist Euler characteristic is the alternating finite-rank sum of the
cohomology of its concrete pullback tensor twist. -/
theorem eulerCharacteristic_def
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData) {d : ℕ}
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)]
    (n : Fin d → ℤ) :
    eulerCharacteristic k f Z L n =
      @Scheme.Hom.eulerCharacteristic k _ Z.subscheme
        (Z.subschemeι ≫ f) inferInstance (pullbackTensorTwist Z L n)
        (@pullbackTensorTwist_isCoherent X Z
          (LocallyOfFiniteType.isLocallyNoetherian (Z.subschemeι ≫ f)) d L _ n) := sorry

/-- The Euler characteristic of the ambient pushforward structure twist equals that of the
corresponding tensor twist restricted to the closed subscheme. -/
theorem eulerCharacteristic_pushforwardStructureTwist_eq
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData) {d : ℕ}
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)]
    (n : Fin d → ℤ) :
    Scheme.Hom.eulerCharacteristic f (pushforwardStructureTwist k f Z L n) =
      eulerCharacteristic k f Z L n := sorry

end AlgebraicGeometry.Scheme.Modules.Intersection
