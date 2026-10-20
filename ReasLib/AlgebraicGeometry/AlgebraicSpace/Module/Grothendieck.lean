module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Original-universe generators of algebraic-space modules

The full chart site has large objects, but its displayed dense atlas charts have an actual
small index. Sheafification of free represented modules on those charts gives a generator
without changing the module section universe.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.AtlasGenerator

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- The genuinely small chart index attached to the atlas already in the input space. -/
abbrev Index : Type u := PullbackFactory.SmallAtlas.Index (AtlasInput.scheme X)

/-- The full-site object represented by an actual member of that chart family. -/
def chart (i : Index X) : smallEtaleSite X :=
  PullbackFactory.SmallAtlas.object (AtlasInput.scheme X) (AtlasInput.map X) i

/-- A free module presheaf represented by the specified chart, in section universe `u`. -/
def freeRepresentable (i : Index X) : PresheafOfModules.{u} (structureSheaf X).obj :=
  (PresheafOfModules.free (structureSheaf X).obj).obj (yoneda.obj (chart X i))

/-- The actual small coproduct of all displayed free represented chart modules. -/
def presheafGenerator : PresheafOfModules.{u} (structureSheaf X).obj :=
  ∐ freeRepresentable X

/-- Sheafification uses the existing actual original-universe adjunction. -/
def generator : X.Modules :=
  (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj (presheafGenerator X)

/-- The original free represented Hom correspondence evaluates at the chart identity. -/
def representedHomEquiv (i : Index X) (M : PresheafOfModules.{u} (structureSheaf X).obj) :
    (freeRepresentable X i ⟶ M) ≃ M.obj (op (chart X i)) :=
  PresheafOfModules.freeYonedaEquiv

/-- A morphism code consists of its actual section functions on the same small chart family. -/
abbrev MapCode (M N : X.Modules) : Type u :=
  ∀ i : Index X, M.val.obj (op (chart X i)) → N.val.obj (op (chart X i))

/-- Encode the supplied module map by restricting its original section functions. -/
def sectionFunctions {M N : X.Modules} (f : M ⟶ N) : MapCode X M N :=
  fun i x ↦ f.val.app (op (chart X i)) x

/-- Dense chart coverage and sheaf separation make the actual section code injective. -/
theorem sectionFunctions_injective (M N : X.Modules) :
    Function.Injective (sectionFunctions X (M := M) (N := N)) := sorry

/-- The actual small-atlas free generator separates maps on the full chart site. -/
theorem generator_isSeparator : IsSeparator (generator X) := sorry

/-- Original module morphisms are small through their specified injective section encoding. -/
theorem locallySmall : LocallySmall.{u} X.Modules where
  hom_small M N := small_of_injective (sectionFunctions_injective X M N)

/-- Filtered sheaf colimits are exact in the original module universe. -/
theorem ab5 : AB5OfSize.{u, u} X.Modules := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.AtlasGenerator

namespace AlgebraicGeometry.AlgebraicSpace

/-- Original-universe module sheaves form a Grothendieck category with the specified
small-atlas generator and the actual sheaf colimits. -/
instance modulesIsGrothendieckAbelian {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsGrothendieckAbelian.{u} X.Modules where
  locallySmall := Modules.AtlasGenerator.locallySmall X
  hasFilteredColimitsOfSize := inferInstance
  ab5OfSize := Modules.AtlasGenerator.ab5 X
  hasSeparator := ⟨Modules.AtlasGenerator.generator X, Modules.AtlasGenerator.generator_isSeparator X⟩

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

/-- The category of quasi-coherent modules on an algebraic space is Grothendieck abelian. -/
instance instIsGrothendieckAbelian {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsGrothendieckAbelian (QCoh X) :=
  sorry

/-- The inclusion of quasi-coherent modules into all module sheaves has a right adjoint. -/
instance inclusionIsLeftAdjoint {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (inclusion X).IsLeftAdjoint :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh
