module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LocallyProjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

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

/-- The support of a section on an étale chart consists of the points where the section
does not vanish on any Zariski neighborhood. -/
def sectionSupport (F : X.Modules) (W : smallEtaleSite X) (s : sectionModule F W) :
    Set W.left.left :=
  {w | ¬ ∃ (V : smallEtaleSite X) (f : V ⟶ W),
    AlgebraicGeometry.IsOpenImmersion f.left.left ∧
      w ∈ Set.range f.left.left.base ∧ F.val.map f.op s = 0}

/-- A point belongs to the support of a section precisely when no open-immersion neighborhood
of that point has zero restriction of the section. -/
theorem mem_sectionSupport_iff (F : X.Modules) (W : smallEtaleSite X)
    (s : sectionModule F W) (w : W.left.left) :
    w ∈ sectionSupport F W s ↔
      ¬ ∃ (V : smallEtaleSite X) (f : V ⟶ W),
        AlgebraicGeometry.IsOpenImmersion f.left.left ∧
          w ∈ Set.range f.left.left.base ∧ F.val.map f.op s = 0 :=
  Iff.rfl

/-- A local section of `F` lies in the range of the closed-support inclusion if and only if it
is sent to zero by the unit `F ⟶ ι_* ι^* F`. -/
theorem mem_range_sectionsWithSupportInι_app_iff (ι : U ⟶ X) [IsOpenImmersion ι]
    (F : X.Modules) (W : smallEtaleSite X) (s : sectionModule F W) :
    s ∈ Set.range ((sectionsWithSupportInι ι F).val.app (op W)) ↔
      ((pullbackPushforwardAdjunction ι).unit.app F).val.app (op W) s = 0 :=
  sorry

/-- On every étale chart, the image of the closed-support inclusion consists exactly of the
sections whose support lies over the complement of the open subspace. -/
theorem range_sectionsWithSupportInι_app_eq_supportedSections (ι : U ⟶ X)
    [IsOpenImmersion ι] (F : X.Modules) (W : smallEtaleSite X)
    {T : Set (Points X)} (hTU : T = (Set.range (Points.map ι))ᶜ) :
    Set.range ((sectionsWithSupportInι ι F).val.app (op W)) =
      {s | sectionSupport F W s ⊆ Points.mapOfOver W.hom ⁻¹' T} :=
  sorry

/-- If `U ⟶ X` is quasi-compact and `T` is the closed complement of `|U|`, then every affine
étale object `W` admits a finitely generated ideal of `𝒪_X(W)` cutting out the preimage of
`T`. -/
theorem exists_fg_ideal_of_quasiCompact_openComplement (ι : U ⟶ X)
    [IsOpenImmersion ι] [QuasiCompact ι]
    {T : Set (Points X)} (hT : IsClosed T)
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
    {T : Set (Points X)} (hT : IsClosed T)
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
