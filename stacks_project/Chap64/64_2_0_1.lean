module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.Definition_59_71_1
public import stacks_project.Chap64.«64_2_0_1_CompactSupport»
public import stacks_project.Chap64.«64_2_0_1_GeometricFrobenius»

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]

section LefschetzTraceFormula
variable {ℓ n : ℕ} [Fact ℓ.Prime]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} (ZMod (ℓ ^ n)))]
variable [CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
    (CategoryTheory.forget (ModuleCat.{u} (ZMod (ℓ ^ n))))]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ {Y : Scheme.{u}}, HasExt (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {Y : Scheme.{u}}, Y.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})]

/-- Finite-type local constancy for a small-étale sheaf of `ZMod (ℓ ^ n)`-modules valued in
`ModuleCat.{u}`, so the coefficient ring may live in `Type` while the sheaf is `u`-large. -/
def IsFiniteTypeLocallyConstantZModSheaf {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))) : Prop :=
  Sheaf.IsLocallyConstantWith
    (fun M : ModuleCat.{u} (ZMod (ℓ ^ n)) ↦ Module.Finite (ZMod (ℓ ^ n)) M) G

/-- Unfolding finite-type local constancy of a `ZMod (ℓ ^ n)`-module sheaf. -/
theorem isFiniteTypeLocallyConstantZModSheaf_iff {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))) :
    IsFiniteTypeLocallyConstantZModSheaf G ↔
      Sheaf.IsLocallyConstantWith
        (fun M : ModuleCat.{u} (ZMod (ℓ ^ n)) ↦ Module.Finite (ZMod (ℓ ^ n)) M) G :=
  sorry

/-- 64.2.0.1: the initial Grothendieck–Lefschetz trace formula proposed in the source.
The source explicitly warns that the cohomological trace terms are not defined for
the stated sheaves, so this proposition records the failure of the preliminary formula
without replacing those terms by a totalized linear-map trace. -/
@[stacks 03SK]
def lefschetzTraceFormula
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (hdim : topologicalKrullDim X.left = 1)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (hF_cons : Sheaf.IsConstructibleEtale
      (fun {Y} f ↦ (zmodSheafPullback f (ℓ ^ n)).obj)
      (fun {Y} G ↦ IsFiniteTypeLocallyConstantZModSheaf G) F) : Prop :=
  False

end LefschetzTraceFormula

end AlgebraicGeometry.Scheme.Etale
