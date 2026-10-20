module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearSystem
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections.OverSpec

/-!
# Vanishing sections of ample modules

This file defines the linear system of tensor-power sections vanishing on a closed subscheme and
states its eventual generation and immersion property on the open complement.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The structure morphism of the open complement of an ideal-sheaf support, obtained by
restricting a given structure morphism. -/
def openComplementToSpec {k : Type u} [Field k] {X : Scheme.{u}}
    (Z : X.IdealSheafData) (f : X ⟶ Spec (CommRingCat.of k)) :
    Z.openComplement.toScheme ⟶ Spec (CommRingCat.of k) :=
  Z.openComplement.ι ≫ f

namespace Scheme.Modules.VanishingSections

variable {X : Scheme.{u}}

/-- The restriction of a tensor power of an invertible module to the complement of an
ideal-sheaf support. -/
noncomputable abbrev tensorPowerOnOpenComplement
    (Z : X.IdealSheafData) (L : X.Modules) [Invertible L] (n : ℕ) :
    Z.openComplement.toScheme.Modules :=
  (pullback Z.openComplement.ι).obj (RingedSpace.TensorPower.sheaf L n)

/-- The restriction of a tensor power of an invertible module to the closed subscheme defined by
ideal-sheaf data. -/
noncomputable abbrev tensorPowerOnClosedSubscheme
    (Z : X.IdealSheafData) (L : X.Modules) [Invertible L] (n : ℕ) :
    Z.subscheme.Modules :=
  (pullback Z.subschemeι).obj (RingedSpace.TensorPower.sheaf L n)

variable {k : Type u} [Field k]

/-- The `k`-linear restriction map from global sections of a tensor power to its pullback on the
closed subscheme. -/
noncomputable def restrictionToClosedSubscheme
    (f : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData)
    (L : X.Modules) [Invertible L] (n : ℕ) :
    Scheme.Hom.globalSectionsMod f (RingedSpace.TensorPower.sheaf L n) ⟶
      Scheme.Hom.globalSectionsMod (Z.subschemeι ≫ f)
        (tensorPowerOnClosedSubscheme Z L n) :=
  globalSectionsPullbackLinear f Z.subschemeι
    (RingedSpace.TensorPower.sheaf L n)

/-- The `k`-linear restriction map from global sections of a tensor power to its pullback on the
open complement. -/
noncomputable def restrictionToOpenComplement
    (f : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData)
    (L : X.Modules) [Invertible L] (n : ℕ) :
    Scheme.Hom.globalSectionsMod f (RingedSpace.TensorPower.sheaf L n) ⟶
      Scheme.Hom.globalSectionsMod (openComplementToSpec Z f)
        (tensorPowerOnOpenComplement Z L n) :=
  globalSectionsPullbackLinear f Z.openComplement.ι
    (RingedSpace.TensorPower.sheaf L n)

/-- The vector subspace of global sections of a tensor power whose restriction to the closed
subscheme vanishes. -/
noncomputable def subspace
    (f : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData)
    (L : X.Modules) [Invertible L] (n : ℕ) :
    Submodule k
      (Scheme.Hom.globalSectionsMod f (RingedSpace.TensorPower.sheaf L n)) :=
  LinearMap.ker (restrictionToClosedSubscheme f Z L n).hom

/-- The bundled linear map restricting a section vanishing on the closed subscheme to the open
complement. -/
noncomputable def toOpenComplement
    (f : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData)
    (L : X.Modules) [Invertible L] (n : ℕ) :
    ModuleCat.of k (subspace f Z L n) ⟶
      Scheme.Hom.globalSectionsMod (openComplementToSpec Z f)
        (tensorPowerOnOpenComplement Z L n) :=
  let source := ModuleCat.of k (subspace f Z L n)
  let target := Scheme.Hom.globalSectionsMod (openComplementToSpec Z f)
    (tensorPowerOnOpenComplement Z L n)
  @ModuleCat.ofHom k _ (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    ((restrictionToOpenComplement f Z L n).hom.comp (subspace f Z L n).subtype)

/-- The vanishing-section linear system generates the restricted tensor power and its canonical
morphism to the projective scheme of that section space is an immersion. -/
def GeneratesAndInducesImmersion
    (f : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData)
    (L : X.Modules) [Invertible L] (n : ℕ) : Prop :=
  ∃ hψ : ProjectiveSpace.VectorSpace.LinearSystem.Generates
      (Over.mk (openComplementToSpec Z f))
      (tensorPowerOnOpenComplement Z L n) (toOpenComplement f Z L n),
    ∃ hP : Scheme.ProjectiveBundle.Representation
      (ProjectiveSpace.VectorSpace.toSpec k (subspace f Z L n))
      (ProjectiveSpace.VectorSpace.moduleSheaf k (subspace f Z L n)),
      IsImmersion
        (@ProjectiveSpace.VectorSpace.LinearSystem.morphism
          k _ (subspace f Z L n) _ _ hP
          (Over.mk (openComplementToSpec Z f))
          (tensorPowerOnOpenComplement Z L n)
          (inferInstanceAs (Invertible
            ((pullback Z.openComplement.ι).obj
              (RingedSpace.TensorPower.sheaf L n))))
          (toOpenComplement f Z L n) hψ)

end Scheme.Modules.VanishingSections

namespace Scheme.Modules.IsAmple

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- On a proper scheme over a field, sections of all sufficiently high tensor powers of an ample
invertible module that vanish on a closed subscheme generate on its complement and induce an
immersive canonical projective morphism. -/
theorem eventualVanishingSectionsGenerateAndInduceImmersion
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (L : X.Modules) [Invertible L] [IsAmple L] (Z : X.IdealSheafData) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      VanishingSections.GeneratesAndInducesImmersion f Z L n := sorry

end Scheme.Modules.IsAmple

end AlgebraicGeometry
