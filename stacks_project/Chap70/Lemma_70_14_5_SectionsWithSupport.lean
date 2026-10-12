/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.Topology.Defs.Basic
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_31_3_LocallyProjective
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism

/-!
# Sections supported on a closed subset of an algebraic space

The sheaf of sections of an `𝒪_X`-module supported in the closed complement of an open
immersion `ι : U ⟶ X` is the kernel of the unit `F ⟶ ι_* ι^* F`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X U : AlgebraicSpace S}

/-- The endofunctor on `X.Modules` sending a module sheaf to the kernel of restriction along an
open immersion `ι : U ⟶ X`. -/
def sectionsWithSupportFunctor (ι : U ⟶ X) [IsOpenImmersion ι] :
    X.Modules ⥤ X.Modules :=
  kernel (pullbackPushforwardAdjunction ι).unit

/-- The sheaf of sections of `F` whose restriction to the open subspace `U` vanishes. -/
def sectionsWithSupportIn (ι : U ⟶ X) [IsOpenImmersion ι] (F : X.Modules) :
    X.Modules :=
  (sectionsWithSupportFunctor ι).obj F

/-- The canonical inclusion of sections supported in the closed complement of `U` into `F`. -/
def sectionsWithSupportInι (ι : U ⟶ X) [IsOpenImmersion ι] (F : X.Modules) :
    sectionsWithSupportIn ι F ⟶ F :=
  (kernel.ι (pullbackPushforwardAdjunction ι).unit).app F

/-- A local section of `F` lies in the range of the closed-support inclusion if and only if it
is sent to zero by the unit `F ⟶ ι_* ι^* F`. When `T` is the closed complement of the image of
`Points.map ι`, this is the condition that the support of the section is contained in the
preimage of `T`. -/
theorem mem_range_sectionsWithSupportInι_app_iff (ι : U ⟶ X) [IsOpenImmersion ι]
    (F : X.Modules) (W : smallEtaleSite X) (s : sectionModule F W) :
    s ∈ Set.range ((sectionsWithSupportInι ι F).val.app (op W)) ↔
      ((pullbackPushforwardAdjunction ι).unit.app F).val.app (op W) s = 0 :=
  sorry

/-- If `U ⟶ X` is quasi-compact and `T` is the closed complement of `|U|`, then every affine
étale object `W` admits a finitely generated ideal of `𝒪_X(W)` cutting out the preimage of
`T`. -/
theorem exists_fg_ideal_of_quasiCompact_openComplement (ι : U ⟶ X)
    [IsOpenImmersion ι] [QuasiCompact ι]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    {T : Set (Points X)} (hT : @IsClosed (Points X) τ T)
    (hTU : T = (Set.range (Points.map ι))ᶜ)
    (W : smallEtaleSite X) [IsAffine W.left.left] :
    ∃ I : Ideal (structureRing W),
      I.FG ∧
        Points.mapOfOver W.hom ⁻¹' T =
          W.left.left.zeroLocus (I : Set (structureRing W)) :=
  sorry

/-- On an affine étale object where the closed complement is cut out by a finitely generated
ideal `I`, the image of the closed-support inclusion consists of the sections annihilated by
some power of `I`. -/
theorem range_sectionsWithSupportInι_app_eq_affine_idealPowerTorsion (ι : U ⟶ X)
    [IsOpenImmersion ι] [QuasiCompact ι]
    (F : X.Modules) [F.IsQuasicoherent]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    {T : Set (Points X)} (hT : @IsClosed (Points X) τ T)
    (hTU : T = (Set.range (Points.map ι))ᶜ)
    (W : smallEtaleSite X) [IsAffine W.left.left]
    (I : Ideal (structureRing W)) (hIfg : I.FG)
    (hI : Points.mapOfOver W.hom ⁻¹' T =
      W.left.left.zeroLocus (I : Set (structureRing W))) :
    Set.range ((sectionsWithSupportInι ι F).val.app (op W)) =
      {x | ∃ n : ℕ, ∀ a, a ∈ I ^ n → a • x = 0} :=
  sorry

/-- If `U ⟶ X` is a quasi-compact open immersion, the sheaf of sections of a quasi-coherent
module supported in the closed complement of `U` is quasi-coherent. -/
instance sectionsWithSupportIn_isQuasicoherent (ι : U ⟶ X)
    [IsOpenImmersion ι] [QuasiCompact ι] (F : X.Modules) [F.IsQuasicoherent] :
    (sectionsWithSupportIn ι F).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

