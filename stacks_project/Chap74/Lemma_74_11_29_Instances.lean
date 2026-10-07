module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage

/-!
# Finite locally free morphisms are fpqc local on the target

Finite locally free morphisms of algebraic spaces over a scheme `S` satisfy
`IsLocalAtTarget` for the fpqc precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- The direct image of the structure sheaf, viewed as a module on the target
algebraic space. -/
noncomputable def pushforwardStructureModule {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Y.Modules :=
  (Modules.pushforward f).obj (SheafOfModules.unit (structureSheaf X) : X.Modules)

end Hom

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is finite locally free
if it is affine and `f_* 𝒪_X` is a finite locally free `𝒪_Y`-module. -/
class FiniteLocallyFree {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop extends Affine f where
  /-- The pushforward structure sheaf is finite locally free. -/
  pushforward_isFiniteLocallyFree :
    SheafOfModules.IsFiniteLocallyFree (Hom.pushforwardStructureModule f)

/-- A morphism of algebraic spaces is finite locally free if and only if it is
affine and its pushforward structure sheaf is finite locally free. -/
theorem finiteLocallyFree_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    FiniteLocallyFree f ↔
      Affine f ∧
        SheafOfModules.IsFiniteLocallyFree (Hom.pushforwardStructureModule f) :=
  sorry

namespace FiniteLocallyFree

/-- The identity morphism of an algebraic space is finite locally free. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : FiniteLocallyFree (𝟙 X) :=
  sorry

/-- A finite locally free morphism is affine and has finite locally free
pushforward structure sheaf. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteLocallyFree f] :
    Affine f ∧
      SheafOfModules.IsFiniteLocallyFree (Hom.pushforwardStructureModule f) :=
  sorry

/-- Finite locally free morphisms of algebraic spaces are local on the target
for the fpqc precoverage. -/
instance isLocalAtTargetFpqc {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@FiniteLocallyFree S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces is finite locally free if and only if every
base change along a member of an fpqc covering of the target is finite locally
free. -/
theorem iff_forall_pullbackSnd_fpqc {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {R : Presieve Y} (hR : R ∈ (fpqcPrecoverage S).coverings Y) :
    FiniteLocallyFree f ↔
      ∀ {U : AlgebraicSpace S} (g : U ⟶ Y) [HasPullback f g],
        R g → FiniteLocallyFree (pullback.snd f g) :=
  sorry

end FiniteLocallyFree

end AlgebraicGeometry.AlgebraicSpace
