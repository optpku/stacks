/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Biproduct
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Section
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Symmetric.Lift
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Realization
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle.Compactification

variable {X E : Scheme.{u}} (C : X.Modules)

/-- The quotient of `C ⊞ 𝟙_ X.Modules` onto its trivial summand. -/
noncomputable def zeroQuotient :
    CategoryTheory.InvertibleQuotient (C ⊞ 𝟙_ X.Modules) where
  object := 𝟙_ X.Modules
  isInvertible := inferInstance
  hom := biprod.snd
  hom_epi := inferInstance

/-- The object of `zeroQuotient C` is the structure module. -/
theorem zeroQuotient_object :
    (zeroQuotient C).object = 𝟙_ X.Modules := sorry

/-- The morphism of `zeroQuotient C` is the second biproduct projection. -/
theorem zeroQuotient_hom :
    (zeroQuotient C).hom = (biprod.snd : C ⊞ 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) := sorry

/-- The lift through a represented projective bundle classified by the quotient onto the
trivial summand. -/
noncomputable def zeroLift (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    ProjectiveBundle.Lift π (𝟙 X) :=
  (ProjectiveBundle.sectionLiftEquiv π hπ).symm (zeroQuotient C)

/-- The quotient associated to `zeroLift` is the quotient onto the trivial summand. -/
theorem zeroLift_spec (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    ProjectiveBundle.sectionLiftEquiv π hπ (zeroLift C π hπ) =
      zeroQuotient C := sorry

/-- The section of the projective compactification defined by the quotient onto the trivial
summand. -/
noncomputable def zeroSection (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) : X ⟶ E :=
  (zeroLift C π hπ).hom

/-- The zero section followed by the projective-bundle projection is the identity. -/
theorem zeroSection_projection (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    zeroSection C π hπ ≫ π = 𝟙 X := sorry

/-- The direct image of the structure module along the zero section. -/
noncomputable def zeroSectionModule (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) : E.Modules :=
  (Scheme.Modules.pushforward (zeroSection C π hπ)).obj (𝟙_ X.Modules)

/-- `zeroSectionModule` is the module pushforward of the structure module along the
zero section. -/
theorem zeroSectionModule_def (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    zeroSectionModule C π hπ =
      (Scheme.Modules.pushforward (zeroSection C π hπ)).obj (𝟙_ X.Modules) := sorry

variable [C.IsQuasicoherent]
variable (V : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra C))
variable [IsRelativeSpectrumOver V]

/-- The quotient morphism on the vector-bundle total space evaluates the module summand at
its universal point and sends the trivial summand identically to the structure module. -/
noncomputable def chartQuotientHom :
    (Scheme.Modules.pullback V.π).obj (C ⊞ 𝟙_ X.Modules) ⟶ 𝟙_ V.scheme.Modules :=
  let hAffine := isAffineHom_of_realizesRelativeSpectrum (SymmetricAlgebra.qcAlgebra C)
    (relativeSpecπ_realizesRelativeSpectrum V)
  let A := @pushforwardStructureSheafQcAlgebra _ _ V.π
    (@instQuasiCompactOfIsAffineHom _ _ V.π hAffine)
    (@IsSeparated.instQuasiSeparated _ _ V.π
      (@IsSeparated.of_isAffineHom _ _ V.π hAffine))
  let evaluation := (Scheme.Modules.pullbackPushforwardAdjunction V.π).homEquiv _ _ |>.symm
    (SymmetricAlgebra.ι C ≫
      QcAlgebraUnder.underlyingModuleMap X (⟨V.universalMap⟩ : SymmetricAlgebra.qcAlgebra C ⟶ A) ≫
      (Scheme.Modules.pushforward V.π).map
        (RingedSpace.unitModuleToTensorUnit V.scheme.toRingedSpace))
  (Scheme.Modules.pullback V.π).map biprod.fst ≫ evaluation +
    (Scheme.Modules.pullback V.π).map biprod.snd ≫ (Scheme.Modules.pullbackUnitIso V.π).hom

/-- The evaluation quotient of the pulled-back module with its trivial summand is
surjective. -/
theorem chartQuotient_epi : Epi (chartQuotientHom C V) := sorry

/-- The invertible quotient associated to the universal vector-bundle point with trivial
coordinate equal to one. -/
noncomputable def chartQuotient :
    CategoryTheory.InvertibleQuotient ((Scheme.Modules.pullback V.π).obj (C ⊞ 𝟙_ X.Modules)) where
  object := 𝟙_ V.scheme.Modules
  isInvertible := inferInstance
  hom := chartQuotientHom C V
  hom_epi := chartQuotient_epi C V

/-- The lift to the projective compactification classified by the universal evaluation
quotient with trivial coordinate one. -/
noncomputable def chartLift (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    ProjectiveBundle.Lift π V.π :=
  (hπ.liftEquiv V.π).symm (chartQuotient C V)

/-- The quotient classified by the vector-bundle lift is the universal evaluation quotient. -/
theorem chartLift_spec (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    hπ.liftEquiv V.π (chartLift C V π hπ) = chartQuotient C V := sorry

/-- The canonical inclusion of a vector bundle into its projective compactification. -/
noncomputable def j (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    associatedVectorBundle C V ⟶ E :=
  (chartLift C V π hπ).hom

/-- The canonical vector-bundle inclusion commutes with the projections to the base. -/
theorem j_projection (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    j C V π hπ ≫ π = associatedVectorBundleπ C V := sorry

/-- The canonical vector-bundle inclusion into the projective compactification is open. -/
theorem j_isOpenImmersion (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    IsOpenImmersion (j C V π hπ) := sorry

/-- The canonical vector-bundle inclusion is flat. -/
theorem j_flat (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    Flat (j C V π hπ) := sorry

/-- The canonical vector-bundle inclusion has relative dimension zero. -/
theorem j_relativeDimension (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    Scheme.Hom.RelativeDimension (j C V π hπ) 0 := sorry

/-- The vector-bundle inclusion commutes with structure morphisms to a further base. -/
theorem j_structure (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules))
    {S : Scheme.{u}} (p : X ⟶ S) :
    j C V π hπ ≫ (π ≫ p) = associatedVectorBundleπ C V ≫ p := sorry

/-- The canonical vector-bundle inclusion as a morphism over a further base. -/
noncomputable def jOver (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules))
    {S : Scheme.{u}} (p : X ⟶ S) :
    Over.mk (associatedVectorBundleπ C V ≫ p) ⟶ Over.mk (π ≫ p) :=
  Over.homMk (j C V π hπ) (j_structure C V π hπ p)

/-- The underlying morphism of the inclusion over a further base is the canonical inclusion. -/
theorem jOver_left (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules))
    {S : Scheme.{u}} (p : X ⟶ S) :
    (jOver C V π hπ p).left = j C V π hπ := sorry

/-- The vector-bundle inclusion over a further base followed by the projective projection
is the vector-bundle projection. -/
theorem jOver_projection (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules))
    {S : Scheme.{u}} (p : X ⟶ S) :
    jOver C V π hπ p ≫ (Over.homMk π : Over.mk (π ≫ p) ⟶ Over.mk p) =
      (Over.homMk (associatedVectorBundleπ C V) :
        Over.mk (associatedVectorBundleπ C V ≫ p) ⟶ Over.mk p) := sorry

end AlgebraicGeometry.Scheme.ProjectiveBundle.Compactification
