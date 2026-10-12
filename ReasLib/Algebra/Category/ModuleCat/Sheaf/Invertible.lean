/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteFreeRetract
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.CategoryTheory.Monoidal.Invertible.Closed
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Invertible modules on a ringed site

This module records the tensor, dual, and evaluation APIs for modules over a
commutative ring sheaf on an arbitrary site.  Its owner is independent of a
specific geometric category.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{w}}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

section Duality

/-- The internal-Hom dual of a module with values in the structure module. -/
@[stacks 040A "(2), dual object", stacks 01CT "(2), dual object"]
abbrev dual
    (L : ringedSiteModuleCategory J 𝒪) [Closed L] : ringedSiteModuleCategory J 𝒪 :=
  (ihom L).obj (SheafOfModules.unit (ringSheaf J 𝒪))

namespace dual

/-- The structure-module-valued internal-Hom dual of an invertible module is invertible. The
`Closed L` input keeps the instance head definitionally aligned with the caller's chosen
internal-Hom structure. -/
@[stacks 040A "(2), dual", stacks 01CT "(2), dual"]
instance isInvertible
    (L : ringedSiteModuleCategory J 𝒪) [Closed L]
    [MonoidalCategory.isInvertibleObject L] :
    MonoidalCategory.isInvertibleObject (dual L) :=
  MonoidalCategory.isInvertibleObject.of_iso
    ((ihom L).mapIso (unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).symm)
    (inferInstance : MonoidalCategory.isInvertibleObject
      ((ihom L).obj (𝟙_ (ringedSiteModuleCategory J 𝒪))))

/-- Evaluation into the structure module is an isomorphism for an invertible module. The
`Closed L` input preserves the caller's chosen evaluation morphism. -/
@[stacks 040A "(2), evaluation", stacks 01CT "(2), evaluation"]
instance evaluationIsIso
    (L : ringedSiteModuleCategory J 𝒪) [Closed L]
    [MonoidalCategory.isInvertibleObject L] :
    IsIso ((ihom.ev L).app (SheafOfModules.unit (ringSheaf J 𝒪))) := by
  let S := SheafOfModules.unit (ringSheaf J 𝒪)
  let u : S ≅ 𝟙_ (ringedSiteModuleCategory J 𝒪) :=
    unitIsoTensorUnit (J := J) (𝒪 := 𝒪)
  -- Local instance justification (proof-local temporary data): the unit normalization is needed to transport evaluation from the tensor unit to the structure module.
  haveI : IsIso u.hom := u.isIso_hom
  have hwhisk : IsIso (L ◁ (ihom L).map u.hom) := by infer_instance
  have heval : IsIso ((ihom.ev L).app (𝟙_ (ringedSiteModuleCategory J 𝒪))) :=
    MonoidalCategory.isInvertibleObject.evaluationIsIso L
  -- Local instance justification (proof-local temporary data): this composite is the transported evaluation map used to recover the evaluation at the structure module.
  haveI : IsIso ((ihom.ev L).app S ≫ u.hom) := by
    rw [← ihom.ev_naturality (A := L) u.hom]
    exact IsIso.comp_isIso' hwhisk heval
  exact IsIso.of_isIso_comp_right ((ihom.ev L).app S) u.hom

/-- Right-tensor equivalence of a module implies right-tensor equivalence of its dual. The
equivalence proof is explicit because this is a bridge from the legacy criterion to the canonical
invertible-object API. -/
@[stacks 040A "(2), right-tensor bridge", stacks 01CT "(2), right-tensor bridge"]
theorem tensorRightIsEquivalence
    (L : ringedSiteModuleCategory J 𝒪) [Closed L]
    (hL : Functor.IsEquivalence (tensorRight L)) :
    Functor.IsEquivalence (tensorRight (dual L)) := by
  -- Local instance justification (proof-local temporary data): `hL` supplies the invertibility witness for the caller's chosen module.
  letI : MonoidalCategory.isInvertibleObject L :=
    MonoidalCategory.isInvertibleObject.ofTensorRight L hL
  -- Local instance justification (proof-local temporary data): the dual invertibility witness is derived from the explicit witness for `L`.
  letI : MonoidalCategory.isInvertibleObject (dual L) := dual.isInvertible L
  infer_instance

/-- A specified tensor inverse of `L` is canonically isomorphic to its
structure-module-valued internal-Hom dual. -/
@[stacks 0B8N "consequence (3)"]
noncomputable def isoOfTensorInverse
    (L N : ringedSiteModuleCategory J 𝒪) [Closed L]
    (e : L ⊗ N ≅ unitModule J 𝒪) : N ≅ dual L :=
  MonoidalClosed.RightInverse.isoIhomUnit L N
      (e ≪≫ unitIsoTensorUnit (J := J) (𝒪 := 𝒪)) ≪≫
    (ihom L).mapIso (unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).symm

/-- The forward map of `isoOfTensorInverse` is the generic tensor-inverse comparison followed
by the internal-Hom image of the tensor-unit normalization. -/
theorem isoOfTensorInverse_hom
    (L N : ringedSiteModuleCategory J 𝒪) [Closed L]
    (e : L ⊗ N ≅ unitModule J 𝒪) :
    (isoOfTensorInverse L N e).hom =
      (MonoidalClosed.RightInverse.isoIhomUnit L N
        (e ≪≫ unitIsoTensorUnit (J := J) (𝒪 := 𝒪))).hom ≫
      ((ihom L).mapIso (unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).symm).hom :=
  rfl

/-- Uncurrying the forward tensor-inverse comparison recovers the normalized evaluation into
the structure module. -/
theorem uncurry_isoOfTensorInverse_hom
    (L N : ringedSiteModuleCategory J 𝒪) [Closed L]
    (e : L ⊗ N ≅ unitModule J 𝒪) :
    uncurry (isoOfTensorInverse L N e).hom =
      (ExactPairing.braidedSwap
        (MonoidalClosed.RightInverse.pairing L N
          (e ≪≫ unitIsoTensorUnit (J := J) (𝒪 := 𝒪)))).evaluation' ≫
        (unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).inv := by
  rw [isoOfTensorInverse_hom, Functor.mapIso_hom,
    MonoidalClosed.uncurry_natural_right,
    MonoidalClosed.RightInverse.uncurry_isoIhomUnit_hom]
  rfl

end dual

end Duality

section Consequences

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C,
  (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- An invertible module sheaf is finitely presented. This is the canonical Mathlib
finite-presentation predicate on the module sheaf itself, not an ambient `Fact` rebuilding the
property on every slice. -/
@[stacks 0B8N "consequence (1), finite presentation"]
instance isFinitePresentation_of_isInvertible
    (L : ringedSiteModuleCategory J 𝒪) [MonoidalCategory.isInvertibleObject L] :
    L.IsFinitePresentation := sorry

variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- An invertible module sheaf is locally a retract of a finite free module sheaf. -/
@[stacks 0B8N "consequence (2)"]
instance FiniteFreeRetract.isLocal_of_isInvertible
    (L : ringedSiteModuleCategory J 𝒪) [MonoidalCategory.isInvertibleObject L] :
    FiniteFreeRetract.IsLocal L := sorry

end Consequences

end SheafOfModules.RingedSite
