/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ZeroScheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Symmetric.Lift
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Affine
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.LineBundle
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The zero section of an associated line bundle

This file constructs the algebraic zero section of the relative-spectrum model associated
to an invertible module and its presentation as a regular zero scheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedVectorBundle

variable {S : Scheme.{u}} (X : Over S)
variable (ℒ : X.left.Modules) [Modules.Invertible ℒ]
variable (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℒ))
variable [IsRelativeSpectrumOver P]

/-- The zero section of the relative-spectrum model of the line bundle associated to `ℒ`. -/
noncomputable def zeroSection :
    X.left ⟶ associatedVectorBundle ℒ P :=
  ((inferInstance : IsRelativeSpectrumOver P).isRepresentedBy).representableBy.homEquiv.symm
    (⟨𝟙 X.left,
      (QcAlgebraUnder.forget X.left).map
        (SymmetricAlgebra.lift ℒ
          (pushforwardStructureSheafQcAlgebra
            (𝟙 X.left : X.left ⟶ X.left)) 0)⟩ :
      relativeSpectrumPair (SymmetricAlgebra.qcAlgebra ℒ) X.left)

/-- Pulling the universal point back along the zero section gives the symmetric-algebra
augmentation induced by the zero module map. -/
theorem zeroSection_spec :
    relativeSpectrumPairPullbackMap (SymmetricAlgebra.qcAlgebra ℒ)
        (zeroSection X ℒ P) (relativeSpecPoint P) =
      (⟨𝟙 X.left,
        (QcAlgebraUnder.forget X.left).map
          (SymmetricAlgebra.lift ℒ
            (pushforwardStructureSheafQcAlgebra
              (𝟙 X.left : X.left ⟶ X.left)) 0)⟩ :
        relativeSpectrumPair (SymmetricAlgebra.qcAlgebra ℒ) X.left) := sorry

/-- The zero section followed by the vector-bundle projection is the identity. -/
theorem zeroSection_projection :
    zeroSection X ℒ P ≫ associatedVectorBundleπ ℒ P = 𝟙 X.left := sorry

/-- The total space of the associated line bundle, regarded over the original base `S`. -/
noncomputable def totalOver : Over S :=
  Over.mk (associatedVectorBundleπ ℒ P ≫ X.hom)

/-- The structure morphism of `totalOver` is the vector-bundle projection followed by
the structure morphism of `X`. -/
theorem totalOver_hom :
    (totalOver X ℒ P).hom = associatedVectorBundleπ ℒ P ≫ X.hom := sorry

/-- The total space remains locally of finite type over `S`. -/
theorem totalOver_locallyOfFiniteType [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType (totalOver X ℒ P).hom := sorry

/-- The vector-bundle projection as a morphism over `S`. -/
noncomputable def projection : totalOver X ℒ P ⟶ X :=
  Over.homMk (associatedVectorBundleπ ℒ P)

/-- The underlying scheme morphism of `projection` is the associated-vector-bundle
projection. -/
theorem projection_left :
    (projection X ℒ P).left = associatedVectorBundleπ ℒ P := sorry

/-- The associated line-bundle projection is flat. -/
theorem projection_flat : Flat (projection X ℒ P).left := sorry

/-- The associated line-bundle projection has relative dimension one. -/
theorem projection_relativeDimension :
    Scheme.Hom.RelativeDimension (projection X ℒ P).left 1 := sorry

/-- The zero section commutes with the structure morphisms to `S`. -/
theorem zeroSection_structure :
    zeroSection X ℒ P ≫ (totalOver X ℒ P).hom = X.hom := sorry

/-- The zero section as a morphism over `S`. -/
noncomputable def zeroSectionOver : X ⟶ totalOver X ℒ P :=
  Over.homMk (zeroSection X ℒ P) (zeroSection_structure X ℒ P)

/-- The underlying scheme morphism of `zeroSectionOver` is `zeroSection`. -/
theorem zeroSectionOver_left :
    (zeroSectionOver X ℒ P).left = zeroSection X ℒ P := sorry

/-- The zero section of an associated line bundle is a closed immersion. -/
theorem zeroSection_isClosedImmersion :
    IsClosedImmersion (zeroSection X ℒ P) := sorry

/-- The over-category zero section is a closed immersion on underlying schemes. -/
theorem zeroSectionOver_isClosedImmersion :
    IsClosedImmersion (zeroSectionOver X ℒ P).left := sorry

/-- The over-category zero section is proper on underlying schemes. -/
theorem zeroSectionOver_isProper :
    IsProper (zeroSectionOver X ℒ P).left := sorry

/-- The inverse line bundle pulled back to the total space. -/
noncomputable def inverseLine : (totalOver X ℒ P).left.Modules :=
  (Modules.pullback (projection X ℒ P).left).obj
    (Modules.tensorPowerInt ℒ (-1))

/-- `inverseLine` is the pullback of the negative first tensor power of `ℒ`. -/
theorem inverseLine_def :
    inverseLine X ℒ P =
      (Modules.pullback (projection X ℒ P).left).obj
        (Modules.tensorPowerInt ℒ (-1)) := sorry

/-- The pulled-back inverse line bundle is invertible. -/
theorem inverseLine_invertible : Modules.Invertible (inverseLine X ℒ P) := sorry

/-- The zero scheme of a section of `inverseLine`, regarded over `S`. -/
noncomputable def zeroSchemeOver (σ : (inverseLine X ℒ P).sections) : Over S :=
  Over.mk
    (@Scheme.zeroSchemeι (totalOver X ℒ P).left _ (inverseLine X ℒ P)
      (Modules.Invertible.tensorRight_isEquivalence (inverseLine_invertible X ℒ P)) σ ≫
        (totalOver X ℒ P).hom)

/-- The structure morphism of `zeroSchemeOver` is its closed immersion followed by the
structure morphism of the total space. -/
theorem zeroSchemeOver_hom (σ : (inverseLine X ℒ P).sections) :
    (zeroSchemeOver X ℒ P σ).hom =
      @Scheme.zeroSchemeι (totalOver X ℒ P).left _ (inverseLine X ℒ P)
          (Modules.Invertible.tensorRight_isEquivalence (inverseLine_invertible X ℒ P)) σ ≫
        (totalOver X ℒ P).hom := sorry

/-- A zero scheme in a locally finite-type total space is locally of finite type over `S`. -/
theorem zeroSchemeOver_locallyOfFiniteType [LocallyOfFiniteType X.hom]
    (σ : (inverseLine X ℒ P).sections) :
    LocallyOfFiniteType (zeroSchemeOver X ℒ P σ).hom := sorry

/-- The zero section is the inclusion of the zero scheme of a regular section of the
pulled-back inverse line bundle. -/
theorem existsRegularZeroScheme :
    ∃ σ : (inverseLine X ℒ P).sections,
      RingedSpace.IsRegularSection (inverseLine X ℒ P) σ ∧
        ∃ e : X ≅ zeroSchemeOver X ℒ P σ,
          e.hom.left ≫
              @Scheme.zeroSchemeι (totalOver X ℒ P).left _ (inverseLine X ℒ P)
                (Modules.Invertible.tensorRight_isEquivalence
                  (inverseLine_invertible X ℒ P)) σ =
            zeroSection X ℒ P := sorry

end AlgebraicGeometry.Scheme.AssociatedVectorBundle
