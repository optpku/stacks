/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Biproduct
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Section
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Symmetric.Lift
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Adjoining the structure module raises the finite local rank by one. -/
instance instIsFiniteLocallyFreeOfRankBiprodUnit
    {X : Scheme.{u}} (C : X.Modules) (r : ℕ) [C.IsFiniteLocallyFreeOfRank r] :
    (C ⊞ 𝟙_ X.Modules).IsFiniteLocallyFreeOfRank (r + 1) := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.AssociatedVectorBundle

variable {X : Scheme.{u}} (C : X.Modules) [C.IsQuasicoherent]
variable (V : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra C))
variable [IsRelativeSpectrumOver V]

/-- The zero section of the relative-spectrum presentation of the vector bundle associated
to `C`. -/
noncomputable def origin : X ⟶ associatedVectorBundle C V :=
  ((inferInstance : IsRelativeSpectrumOver V).isRepresentedBy).representableBy.homEquiv.symm
    (⟨𝟙 X,
      (QcAlgebraUnder.forget X).map
        (SymmetricAlgebra.lift C
          (pushforwardStructureSheafQcAlgebra (𝟙 X : X ⟶ X)) 0)⟩ :
      relativeSpectrumPair (SymmetricAlgebra.qcAlgebra C) X)

/-- Pulling the universal point back along `origin` gives the augmentation induced by the
zero module map. -/
theorem origin_spec :
    relativeSpectrumPairPullbackMap (SymmetricAlgebra.qcAlgebra C)
        (origin C V) (relativeSpecPoint V) =
      (⟨𝟙 X,
        (QcAlgebraUnder.forget X).map
          (SymmetricAlgebra.lift C
            (pushforwardStructureSheafQcAlgebra (𝟙 X : X ⟶ X)) 0)⟩ :
        relativeSpectrumPair (SymmetricAlgebra.qcAlgebra C) X) := sorry

/-- The origin is a section of the associated-vector-bundle projection. -/
theorem origin_projection :
    origin C V ≫ associatedVectorBundleπ C V = 𝟙 X := sorry

end AlgebraicGeometry.Scheme.AssociatedVectorBundle

namespace AlgebraicGeometry.Scheme.ProjectiveBundle.Compactification

variable {X E : Scheme.{u}} (C : X.Modules)

/-- The quotient of `C ⊞ 𝟙_ X.Modules` onto its trivial summand. -/
noncomputable def infinityQuotient :
    CategoryTheory.InvertibleQuotient (C ⊞ 𝟙_ X.Modules) where
  object := 𝟙_ X.Modules
  isInvertible := inferInstance
  hom := biprod.snd
  hom_epi := inferInstance

/-- The object of `infinityQuotient C` is the structure module. -/
theorem infinityQuotient_object :
    (infinityQuotient C).object = 𝟙_ X.Modules := sorry

/-- The morphism of `infinityQuotient C` is the second biproduct projection. -/
theorem infinityQuotient_hom :
    (infinityQuotient C).hom = (biprod.snd : C ⊞ 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) := sorry

/-- The lift through a represented projective bundle classified by the quotient onto the
trivial summand. -/
noncomputable def infinityLift (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    ProjectiveBundle.Lift π (𝟙 X) :=
  (ProjectiveBundle.sectionLiftEquiv π hπ).symm (infinityQuotient C)

/-- The quotient associated to `infinityLift` is the quotient onto the trivial summand. -/
theorem infinityLift_spec (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    ProjectiveBundle.sectionLiftEquiv π hπ (infinityLift C π hπ) =
      infinityQuotient C := sorry

/-- The section of the projective compactification defined by the quotient onto the trivial
summand. -/
noncomputable def infinitySection (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) : X ⟶ E :=
  (infinityLift C π hπ).hom

/-- The infinity section followed by the projective-bundle projection is the identity. -/
theorem infinitySection_projection (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    infinitySection C π hπ ≫ π = 𝟙 X := sorry

/-- The direct image of the structure module along the infinity section. -/
noncomputable def infinityStructureSheaf (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) : E.Modules :=
  (Scheme.Modules.pushforward (infinitySection C π hπ)).obj (𝟙_ X.Modules)

/-- `infinityStructureSheaf` is the module pushforward of the structure module along the
infinity section. -/
theorem infinityStructureSheaf_def (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    infinityStructureSheaf C π hπ =
      (Scheme.Modules.pushforward (infinitySection C π hπ)).obj (𝟙_ X.Modules) := sorry

/-- The morphism from the structure module to the tautological module induced by the trivial
summand of `C ⊞ 𝟙_ X.Modules`. -/
noncomputable def trivialCoordinateHom (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    𝟙_ E.Modules ⟶ ProjectiveBundle.tautologicalSheaf π hπ :=
  (Scheme.Modules.pullbackUnitIso π).inv ≫
    (Scheme.Modules.pullback π).map
      (biprod.inr : 𝟙_ X.Modules ⟶ C ⊞ 𝟙_ X.Modules) ≫
    (ProjectiveBundle.tautologicalQuotient π hπ).hom

/-- The trivial-coordinate morphism is the pullback of the trivial-summand inclusion followed
by the tautological quotient. -/
theorem trivialCoordinateHom_def (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    trivialCoordinateHom C π hπ =
      (Scheme.Modules.pullbackUnitIso π).inv ≫
        (Scheme.Modules.pullback π).map
          (biprod.inr : 𝟙_ X.Modules ⟶ C ⊞ 𝟙_ X.Modules) ≫
        (ProjectiveBundle.tautologicalQuotient π hπ).hom := sorry

/-- The global section of the tautological module given by the trivial-summand coordinate
`T`. -/
noncomputable def trivialCoordinate (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    Γ(ProjectiveBundle.tautologicalSheaf π hπ, ⊤) :=
  RingedSpace.sectionsEquivTop (ProjectiveBundle.tautologicalSheaf π hπ)
    ((ProjectiveBundle.tautologicalSheaf π hπ).unitHomEquiv
      ((RingedSpace.unitIsoTensorUnit E.toRingedSpace).hom ≫
        trivialCoordinateHom C π hπ))

/-- The top-open value of the trivial coordinate is classified by `trivialCoordinateHom`. -/
theorem trivialCoordinate_spec (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    (ProjectiveBundle.tautologicalSheaf π hπ).unitHomEquiv.symm
        (RingedSpace.sectionFromTop (ProjectiveBundle.tautologicalSheaf π hπ)
          (trivialCoordinate C π hπ)) =
      (RingedSpace.unitIsoTensorUnit E.toRingedSpace).hom ≫
        trivialCoordinateHom C π hπ := sorry

/-- The canonical standard open `T ≠ 0` in the projective compactification, defined as the
nonvanishing open of the tautological section coming from the trivial summand. -/
noncomputable def trivialCoordinateOpen (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) : E.Opens :=
  (ProjectiveBundle.tautologicalSheaf_isInvertible π hπ).sectionNonvanishingOpen
    (trivialCoordinate C π hπ)

/-- The canonical compactification open is the nonvanishing open of the trivial coordinate. -/
theorem trivialCoordinateOpen_def (π : E ⟶ X)
    (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules)) :
    trivialCoordinateOpen C π hπ =
      (ProjectiveBundle.tautologicalSheaf_isInvertible π hπ).sectionNonvanishingOpen
        (trivialCoordinate C π hπ) := sorry

variable [C.IsQuasicoherent]
variable (V : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra C))
variable [IsRelativeSpectrumOver V]
variable (π : E ⟶ X) (hπ : ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules))

/-- An explicit presentation of the vector bundle as the affine chart of its projective
compactification. Its open is required to be the canonical standard open `T ≠ 0`, and the
identification is compatible with the projections and their distinguished sections. -/
structure AffineChart where
  /-- The affine-chart open subscheme of the compactification. -/
  U : E.Opens
  /-- The chart open is the standard open cut out by the trivial-summand coordinate. -/
  standardOpen : U = trivialCoordinateOpen C π hπ
  /-- The identification of the vector bundle with the chosen open subscheme. -/
  iso : associatedVectorBundle C V ≅ U.toScheme
  /-- The chart identification is over `X`. -/
  projection_compatibility :
    iso.hom ≫ U.ι ≫ π = associatedVectorBundleπ C V
  /-- The vector-bundle origin corresponds to the infinity section in the chart. -/
  origin_compatibility :
    AssociatedVectorBundle.origin C V ≫ iso.hom ≫ U.ι = infinitySection C π hπ

namespace AffineChart

/-- Construct the canonical affine chart from the trivial-coordinate standard open, an
identification with the vector bundle, and the two source compatibilities. -/
def ofOpenIso (U : E.Opens) (standardOpen : U = trivialCoordinateOpen C π hπ)
    (iso : associatedVectorBundle C V ≅ U.toScheme)
    (projection_compatibility : iso.hom ≫ U.ι ≫ π = associatedVectorBundleπ C V)
    (origin_compatibility :
      AssociatedVectorBundle.origin C V ≫ iso.hom ≫ U.ι = infinitySection C π hπ) :
    AffineChart C V π hπ where
  U := U
  standardOpen := standardOpen
  iso := iso
  projection_compatibility := projection_compatibility
  origin_compatibility := origin_compatibility

/-- The open immersion of the vector bundle into its projective compactification. -/
def j (A : AffineChart C V π hπ) : associatedVectorBundle C V ⟶ E :=
  A.iso.hom ≫ A.U.ι

/-- An affine chart is the trivial-coordinate standard open and records both projection
compatibility and compatibility of the two distinguished sections. -/
theorem spec (A : AffineChart C V π hπ) :
    A.U = trivialCoordinateOpen C π hπ ∧
      A.j ≫ π = associatedVectorBundleπ C V ∧
        AssociatedVectorBundle.origin C V ≫ A.j = infinitySection C π hπ := sorry

/-- The chart inclusion commutes with the projections to `X`. -/
theorem j_projection (A : AffineChart C V π hπ) :
    A.j ≫ π = associatedVectorBundleπ C V := sorry

/-- The chart inclusion is flat. -/
theorem j_flat (A : AffineChart C V π hπ) : Flat A.j := sorry

/-- The chart inclusion has relative dimension zero. -/
theorem j_relativeDimension (A : AffineChart C V π hπ) :
    Scheme.Hom.RelativeDimension A.j 0 := sorry

/-- The chart inclusion commutes with the structure morphisms to a further base. -/
theorem j_structure (A : AffineChart C V π hπ) {S : Scheme.{u}} (p : X ⟶ S) :
    A.j ≫ (π ≫ p) = associatedVectorBundleπ C V ≫ p := sorry

/-- The affine-chart inclusion as a morphism over a further base scheme. -/
def jOver (A : AffineChart C V π hπ) {S : Scheme.{u}} (p : X ⟶ S) :
    Over.mk (associatedVectorBundleπ C V ≫ p) ⟶ Over.mk (π ≫ p) :=
  Over.homMk A.j (j_structure C V π hπ A p)

/-- The underlying scheme morphism of `jOver` is the affine-chart inclusion. -/
theorem jOver_left (A : AffineChart C V π hπ) {S : Scheme.{u}} (p : X ⟶ S) :
    (jOver C V π hπ A p).left = A.j := sorry

/-- The chart inclusion over a further base followed by the projective projection is the
vector-bundle projection. -/
theorem jOver_projection (A : AffineChart C V π hπ) {S : Scheme.{u}} (p : X ⟶ S) :
    jOver C V π hπ A p ≫ (Over.homMk π : Over.mk (π ≫ p) ⟶ Over.mk p) =
      (Over.homMk (associatedVectorBundleπ C V) :
        Over.mk (associatedVectorBundleπ C V ≫ p) ⟶ Over.mk p) := sorry

end AffineChart

end AlgebraicGeometry.Scheme.ProjectiveBundle.Compactification
