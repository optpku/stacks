module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Lemma_67_4_8
public import stacks_project.Chap67.Lemma_67_23_2
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
import stacks_project.Chap67.Definition_67_48_3_RelativeSpectrum
import stacks_project.Chap76.Definition_76_6_5_Symmetric

/-!
# Associated line bundle of an invertible module on an algebraic space

The total space of an invertible `𝒪_X`-module is the relative spectrum of its
symmetric algebra. Relative spectrum is imported privately so this owner can
be loaded beside Chow groups.
-/

public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- An invertible module on an algebraic space is quasi-coherent. -/
instance instIsQuasicoherent_of_isInvertibleObject (L : X.Modules)
    [isInvertibleObject L] : L.IsQuasicoherent :=
  sorry

/-- The associated vector bundle of an invertible `𝒪_X`-module. -/
noncomputable def associatedVectorBundle (L : X.Modules) [isInvertibleObject L] :
    AlgebraicSpace S :=
  relativeSpec (SymmetricAlgebra.qcAlgebra L)

/-- The structure morphism of the associated vector bundle of an invertible
`𝒪_X`-module. -/
noncomputable def associatedVectorBundleπ (L : X.Modules) [isInvertibleObject L] :
    associatedVectorBundle L ⟶ X :=
  relativeSpecπ (SymmetricAlgebra.qcAlgebra L)

/-- The structure morphism of the associated vector bundle is flat. -/
instance instFlat_associatedVectorBundleπ (L : X.Modules)
    [isInvertibleObject L] : Flat (associatedVectorBundleπ L) :=
  sorry

/-- The structure morphism of the associated vector bundle has relative
dimension `1`. -/
instance instRelativeDimension_associatedVectorBundleπ (L : X.Modules)
    [isInvertibleObject L] : RelativeDimension (associatedVectorBundleπ L) 1 :=
  sorry

/-- The structure morphism of the associated vector bundle is quasi-separated. -/
instance instQuasiSeparated_associatedVectorBundleπ (L : X.Modules)
    [isInvertibleObject L] : QuasiSeparated (associatedVectorBundleπ L) :=
  sorry

/-- The structure morphism of the associated vector bundle is locally of finite
type. -/
instance instLocallyOfFiniteType_associatedVectorBundleπ (L : X.Modules)
    [isInvertibleObject L] : LocallyOfFiniteType (associatedVectorBundleπ L) :=
  sorry

/-- Composition of the associated-vector-bundle projection with a quasi-separated
morphism remains quasi-separated. -/
instance instQuasiSeparated_associatedVectorBundleπ_comp {B : AlgebraicSpace S}
    (pX : X ⟶ B) (L : X.Modules) [isInvertibleObject L] [QuasiSeparated pX] :
    QuasiSeparated (associatedVectorBundleπ L ≫ pX) :=
  quasiSeparated_comp (associatedVectorBundleπ L) pX

/-- Composition of the associated-vector-bundle projection with a locally finite
type morphism remains locally of finite type. -/
instance instLocallyOfFiniteType_associatedVectorBundleπ_comp
    {B : AlgebraicSpace S} (pX : X ⟶ B) (L : X.Modules) [isInvertibleObject L]
    [LocallyOfFiniteType pX] :
    LocallyOfFiniteType (associatedVectorBundleπ L ≫ pX) :=
  locallyOfFiniteType_comp (associatedVectorBundleπ L) pX

end AlgebraicGeometry.AlgebraicSpace
