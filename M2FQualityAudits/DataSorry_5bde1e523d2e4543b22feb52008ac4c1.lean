module

import Lean

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import stacks_project.Chap39.Example_39_5_3_Additive_group_scheme_Group
public import stacks_project.Chap39.Lemma_39_4_4

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry MonoidalCategory CategoryTheory.MonObj

universe u v

namespace MvPolynomial.PthPowerKernel

/-- The homogeneous polynomial `X₀ ^ p + α * X₁ ^ p` defining the p-th-power kernel. -/
def relation {k : Type u} [CommRing k] (p : ℕ) (α : k) :
    MvPolynomial (Fin 2) k :=
  X (0 : Fin 2) ^ p + C α * X (1 : Fin 2) ^ p

/-- Evaluating `relation p α` gives the equation `x₀ ^ p + α * x₁ ^ p`. -/
theorem eval_relation {k : Type u} [CommRing k] {A : Type v} [CommRing A]
    (f : k →+* A) (x : Fin 2 → A) (p : ℕ) (α : k) :
    eval₂ f x (relation p α) = x 0 ^ p + f α * x 1 ^ p := sorry

/-- The coordinate ring of the closed subscheme cut out by `relation p α`. -/
abbrev Ring {k : Type u} [CommRing k] (p : ℕ) (α : k) :=
  MvPolynomial (Fin 2) k ⧸
    Ideal.span ({relation p α} : Set (MvPolynomial (Fin 2) k))

/-- The defining relation vanishes in `Ring p α`. -/
theorem quotient_relation_eq_zero {k : Type u} [CommRing k] (p : ℕ) (α : k) :
    Ideal.Quotient.mk (Ideal.span ({relation p α} : Set (MvPolynomial (Fin 2) k)))
        (relation p α) = (0 : Ring p α) := sorry

/-- If `α` is not a p-th power, the coordinate ring of the kernel is a domain. -/
theorem isDomain (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
    (α : k) (hα : α ∉ Set.range (fun β : k ↦ β ^ p)) :
    IsDomain (Ring p α) := sorry

end MvPolynomial.PthPowerKernel

namespace AlgebraicGeometry.PthPowerKernel

open AffineSpace
open MvPolynomial.PthPowerKernel

/-- The p-th-power kernel viewed as a scheme over `Spec k`. -/
def over {k : Type u} [CommRing k] (p : ℕ) (α : k) :
    Over (Spec (CommRingCat.of.{u} k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (Ring p α))))

/-- The underlying affine scheme `V(X₀ ^ p + α * X₁ ^ p)`. -/
abbrev scheme {k : Type u} [CommRing k] (p : ℕ) (α : k) : Scheme :=
  (over p α).left

/-- The structure morphism of `scheme p α` to `Spec k`. -/
abbrev toBase {k : Type u} [CommRing k] (p : ℕ) (α : k) :
    scheme p α ⟶ Spec (CommRingCat.of.{u} k) :=
  (over p α).hom

/-- The ambient affine plane over `Spec k`, equipped with its coordinatewise additive group
scheme structure. -/
abbrev ambient {k : Type u} [CommRing k] : Over (Spec (CommRingCat.of.{u} k)) :=
  Scheme.asOver (𝔸(ULift.{u} (Fin 2); Spec (CommRingCat.of.{u} k)))
    (Spec (CommRingCat.of.{u} k))

/-- The coordinate presentation `Spec k[X₀, X₁]` agrees with the affine plane indexed by
`ULift (Fin 2)`. -/
noncomputable def planeSpecIso {k : Type u} [CommRing k] :
    Spec (CommRingCat.of (MvPolynomial (Fin 2) k)) ≅
      Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k)) :=
  let e : CommRingCat.of (MvPolynomial (Fin 2) k) ≅
      CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k) :=
    (MvPolynomial.renameEquiv k
      (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2))).toCommRingCatIso
  Scheme.Spec.mapIso e.symm.op

/-- The quotient-presentation inclusion into `Spec k[X₀, X₁]`. -/
def inclusionToSpec {k : Type u} [CommRing k] (p : ℕ) (α : k) :
    scheme p α ⟶ Spec (CommRingCat.of (MvPolynomial (Fin 2) k)) :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (Ideal.span ({relation p α} : Set (MvPolynomial (Fin 2) k))))
  )

/-- The quotient presentation identifies `scheme p α` with a closed subscheme of the affine
plane over `Spec k`. -/
def inclusion {k : Type u} [CommRing k] (p : ℕ) (α : k) :
    over p α ⟶ ambient :=
  Over.homMk
    (inclusionToSpec p α ≫ planeSpecIso.hom ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin 2)) (CommRingCat.of.{u} k)).inv)
    (by sorry)

/-- The quotient presentation is a closed immersion into `Spec k[X₀, X₁]`. -/
instance inclusionToSpec_isClosedImmersion {k : Type u} [CommRing k] (p : ℕ) (α : k) :
    IsClosedImmersion (inclusionToSpec p α) := by
  let I : Ideal (CommRingCat.of (MvPolynomial (Fin 2) k)) :=
    Ideal.span ({relation p α} : Set (MvPolynomial (Fin 2) k))
  change IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The p-th-power kernel is a closed subscheme of the affine-plane additive group scheme. -/
instance inclusion_isClosedImmersion {k : Type u} [CommRing k] (p : ℕ) (α : k) :
    IsClosedImmersion (inclusion p α).left := by
  change IsClosedImmersion
      (inclusionToSpec p α ≫ planeSpecIso.hom ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin 2)) (CommRingCat.of.{u} k)).inv)
  infer_instance

section GroupStructure

variable (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] (α : k)

/-- The unit of the additive group scheme factors through the p-th-power kernel. -/
def oneLeft :
    (𝟙_ (Over (Spec (CommRingCat.of.{u} k)))).left ⟶ scheme p α :=
  let G : Over (Spec (CommRingCat.of.{u} k)) := ambient
  let f : (𝟙_ (Over (Spec (CommRingCat.of.{u} k)))).left ⟶
      Spec (CommRingCat.of (MvPolynomial (Fin 2) k)) :=
    η[G].left ≫ (AffineSpace.SpecIso (ULift.{u} (Fin 2)) (CommRingCat.of.{u} k)).hom ≫
      planeSpecIso.inv
  Scheme.Hom.liftQuotient f
    (Ideal.span ({relation p α} : Set (MvPolynomial (Fin 2) k)))
    (by sorry)

/-- Restricted addition on the affine plane factors through the p-th-power kernel. -/
def mulLeft :
    (over p α ⊗ over p α).left ⟶ scheme p α :=
  let G : Over (Spec (CommRingCat.of.{u} k)) := ambient
  let f : (over p α ⊗ over p α).left ⟶
      Spec (CommRingCat.of (MvPolynomial (Fin 2) k)) :=
    (((inclusion p α ⊗ₘ inclusion p α) ≫ μ[G]).left ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin 2)) (CommRingCat.of.{u} k)).hom ≫
      planeSpecIso.inv)
  Scheme.Hom.liftQuotient f
    (Ideal.span ({relation p α} : Set (MvPolynomial (Fin 2) k)))
    (by sorry)

/-- Restricted inversion on the affine plane factors through the p-th-power kernel. -/
def invLeft :
    (over p α).left ⟶ scheme p α :=
  let G : Over (Spec (CommRingCat.of.{u} k)) := ambient
  let f : (over p α).left ⟶ Spec (CommRingCat.of (MvPolynomial (Fin 2) k)) :=
    ((inclusion p α).left ≫ ι[G].left ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin 2)) (CommRingCat.of.{u} k)).hom ≫
      planeSpecIso.inv)
  Scheme.Hom.liftQuotient f
    (Ideal.span ({relation p α} : Set (MvPolynomial (Fin 2) k)))
    (by sorry)

/-- The factored unit of the p-th-power kernel over `Spec k`. -/
def oneHom :
    𝟙_ (Over (Spec (CommRingCat.of.{u} k))) ⟶ over p α :=
  Over.homMk (oneLeft p α) (by sorry)

/-- The factored multiplication of the p-th-power kernel over `Spec k`. -/
def mulHom :
    over p α ⊗ over p α ⟶ over p α :=
  Over.homMk (mulLeft p α) (by sorry)

/-- The factored inverse of the p-th-power kernel over `Spec k`. -/
def invHom :
    over p α ⟶ over p α :=
  Over.homMk (invLeft p α) (by sorry)

/-- The p-th-power kernel carries the induced group-object structure from the affine-plane
additive group scheme. -/
def factorization :
    GrpObj.Factorization (inclusion p α) where
  one := oneHom p α
  mul := mulHom p α
  inv := invHom p α
  one_hom := by sorry
  mul_hom := by sorry
  inv_hom := by sorry

instance inclusion_mono : Mono (inclusion p α) := by
  infer_instance

/-- The p-th-power kernel inherits its canonical group-scheme structure from the ambient affine
plane additive group scheme. -/
instance instGrpObjOver : GrpObj (over p α) :=
  (factorization p α).toGrpObj

/-- The inclusion of the p-th-power kernel into the affine plane is a group-object morphism. -/
instance inclusion_isMonHom : IsMonHom (inclusion p α) :=
  { one_hom := (factorization p α).one_hom
    mul_hom := (factorization p α).mul_hom }

end GroupStructure

/-- The closed subgroup scheme
`V(X₀ ^ p + α * X₁ ^ p) ⊂ 𝔾_a^2`
over `Spec k`. -/
@[stacks 047Q]
noncomputable abbrev closedSubgroup (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
    (α : k) :
    Scheme.ClosedSubgroup (ambient : Over (Spec (CommRingCat.of.{u} k))) :=
  Scheme.ClosedSubgroup.mk (inclusion p α)

/-- The inclusion of `closedSubgroup p α` is the defining closed immersion into the affine
plane. -/
theorem closedSubgroup_inclusion (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
    (α : k) :
    (closedSubgroup p α).inclusion = inclusion p α := by
  simpa [closedSubgroup, Scheme.ClosedSubgroup.inclusion] using
    (Scheme.ClosedSubgroup.mk_hom (i := inclusion p α))

/-- Remark 39.8.5 (1): If `α` is not a p-th power, the p-th-power kernel is integral,
and hence reduced and irreducible. -/
@[stacks 047Q]
theorem isIntegral (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
    (α : k) (hα : α ∉ Set.range (fun β : k ↦ β ^ p)) :
    IsIntegral (scheme p α) := sorry

/-- The p-th-power kernel is integral whenever `α` is not a p-th power. -/
instance instIsIntegralOfNotPthPower (p : ℕ) [Fact p.Prime]
    {k : Type u} [Field k] [CharP k p] (α : k)
    [hα : Fact (α ∉ Set.range (fun β : k ↦ β ^ p))] :
    IsIntegral (scheme p α) :=
  isIntegral p α hα.out

/-- Remark 39.8.5 (2): The structure morphism of the p-th-power kernel is not smooth. -/
@[stacks 047Q]
theorem not_smooth (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
    (α : k) (hα : α ∉ Set.range (fun β : k ↦ β ^ p)) :
    ¬ Smooth (toBase p α) := sorry

/-- Remark 39.8.5 (3): The p-th-power kernel is not normal. -/
@[stacks 047Q]
theorem not_normal (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
    (α : k) (hα : α ∉ Set.range (fun β : k ↦ β ^ p)) :
    ¬ (scheme p α).isNormal := sorry

/-- Integrality of the p-th-power kernel gives the stated reducedness. -/
theorem isReduced (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
    (α : k) (hα : α ∉ Set.range (fun β : k ↦ β ^ p)) :
    IsReduced (scheme p α) :=
  (isIntegral_iff_irreducibleSpace_and_isReduced (scheme p α)).mp (isIntegral p α hα) |>.2

/-- Integrality of the p-th-power kernel gives the stated irreducibility. -/
theorem irreducibleSpace (p : ℕ) [Fact p.Prime]
    {k : Type u} [Field k] [CharP k p]
    (α : k) (hα : α ∉ Set.range (fun β : k ↦ β ^ p)) :
    IrreducibleSpace (scheme p α) :=
  (isIntegral_iff_irreducibleSpace_and_isReduced (scheme p α)).mp (isIntegral p α hα) |>.1

end AlgebraicGeometry.PthPowerKernel


namespace M2FDataSorryAudit

open Lean Meta Elab Command

private def containsNonPropSorry (value : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  forEachExpr value fun expr => do
    unless ← found.get do
      let (head, args) := expr.getAppFnArgs
      if head == ``sorryAx && args.size >= 1 then
        unless ← isProp args[0]! do
          found.set true
  found.get

run_cmd do
  let env ← getEnv
  -- `env.constants` also contains imported declarations.  Current-module
  -- declarations are the ones without a `const2ModIdx` entry; restricting the
  -- scan to them is important for remote compilation because `mkModuleData`
  -- materializes and traverses the entire imported environment.  That made a
  -- tiny audit scratch file hit Leanfra's cancellation deadline on large repos.
  for (name, info) in env.constants do
    if (Environment.getModuleIdxFor? env name).isNone then
      if let some value := info.value? true then
        let (hasNonPropSorry, _) ← liftCoreM <| (containsNonPropSorry value).run
        if hasNonPropSorry then
          logInfo m!"M2F_NON_PROP_DATA_SORRY|{privateToUserName name}"

end M2FDataSorryAudit
