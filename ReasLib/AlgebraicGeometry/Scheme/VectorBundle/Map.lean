module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Dual
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Symmetric.Map
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.ChosenMap
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.FiniteLocallyFree

/-!
# Maps and subbundles of associated vector bundles
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

namespace AssociatedVectorBundle

variable {S : Scheme.{u}} (X : Over S)
variable {F G : X.left.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]

/-- The total space of an associated vector bundle, regarded as a scheme over `S`. -/
noncomputable def over (F : X.left.Modules) [F.IsQuasicoherent]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra F))
    [IsRelativeSpectrumOver P] : Over S :=
  Over.mk (associatedVectorBundleπ F P ≫ X.hom)

/-- The structure morphism of `over` is the vector-bundle projection followed by `X.hom`. -/
theorem over_hom (F : X.left.Modules) [F.IsQuasicoherent]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra F))
    [IsRelativeSpectrumOver P] :
    (over X F P).hom = associatedVectorBundleπ F P ≫ X.hom := sorry

/-- The associated-vector-bundle projection as a morphism over `S`. -/
noncomputable def projectionOver (F : X.left.Modules) [F.IsQuasicoherent]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra F))
    [IsRelativeSpectrumOver P] : over X F P ⟶ X :=
  Over.homMk (associatedVectorBundleπ F P)

/-- The underlying scheme morphism of `projectionOver` is the vector-bundle projection. -/
theorem projectionOver_left (F : X.left.Modules) [F.IsQuasicoherent]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra F))
    [IsRelativeSpectrumOver P] :
    (projectionOver X F P).left = associatedVectorBundleπ F P := sorry

/-- A module map induces a contravariant map of its associated vector-bundle models. -/
noncomputable def map (f : F ⟶ G)
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra F))
    [IsRelativeSpectrumOver P]
    (Q : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra G))
    [IsRelativeSpectrumOver Q] :
    associatedVectorBundle G Q ⟶ associatedVectorBundle F P :=
  relativeSpecMap (SymmetricAlgebra.map f) P Q

/-- The associated-vector-bundle map is the relative-spectrum map induced by the symmetric
algebra morphism. -/
theorem map_def (f : F ⟶ G)
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra F))
    [IsRelativeSpectrumOver P]
    (Q : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra G))
    [IsRelativeSpectrumOver Q] :
    _root_.AlgebraicGeometry.Scheme.AssociatedVectorBundle.map X f P Q =
      relativeSpecMap (SymmetricAlgebra.map f) P Q := sorry

/-- The associated-vector-bundle map commutes with the projections to `X.left`. -/
theorem map_projection (f : F ⟶ G)
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra F))
    [IsRelativeSpectrumOver P]
    (Q : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra G))
    [IsRelativeSpectrumOver Q] :
    _root_.AlgebraicGeometry.Scheme.AssociatedVectorBundle.map X f P Q ≫
      associatedVectorBundleπ F P =
      associatedVectorBundleπ G Q := sorry

/-- The associated-vector-bundle map commutes with the structure morphisms to `S`. -/
theorem map_structure (f : F ⟶ G)
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra F))
    [IsRelativeSpectrumOver P]
    (Q : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra G))
    [IsRelativeSpectrumOver Q] :
    _root_.AlgebraicGeometry.Scheme.AssociatedVectorBundle.map X f P Q ≫
      (over X F P).hom = (over X G Q).hom := sorry

/-- The map of associated vector bundles, regarded as a morphism over `S`. -/
noncomputable def mapOver (f : F ⟶ G)
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra F))
    [IsRelativeSpectrumOver P]
    (Q : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra G))
    [IsRelativeSpectrumOver Q] : over X G Q ⟶ over X F P :=
  Over.homMk (_root_.AlgebraicGeometry.Scheme.AssociatedVectorBundle.map X f P Q)
    (map_structure X f P Q)

/-- The underlying scheme morphism of `mapOver` is the associated-vector-bundle map. -/
theorem mapOver_left (f : F ⟶ G)
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra F))
    [IsRelativeSpectrumOver P]
    (Q : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra G))
    [IsRelativeSpectrumOver Q] :
    (mapOver X f P Q).left =
      _root_.AlgebraicGeometry.Scheme.AssociatedVectorBundle.map X f P Q := sorry

namespace ShortExact

variable (C : ShortComplex X.left.Modules)
variable [C.X₁.IsFiniteLocallyFree] [C.X₂.IsFiniteLocallyFree]
variable (P₁ : RelativeSpectrumOver
  (SymmetricAlgebra.qcAlgebra (Modules.dual C.X₁)))
variable [IsRelativeSpectrumOver P₁]
variable (P₂ : RelativeSpectrumOver
  (SymmetricAlgebra.qcAlgebra (Modules.dual C.X₂)))
variable [IsRelativeSpectrumOver P₂]

/-- The map `V((C.X₁)ᵛ) ⟶ V((C.X₂)ᵛ)` induced by the first arrow of a short
complex. -/
noncomputable def embedding :
    associatedVectorBundle (Modules.dual C.X₁) P₁ ⟶
      associatedVectorBundle (Modules.dual C.X₂) P₂ :=
  _root_.AlgebraicGeometry.Scheme.AssociatedVectorBundle.map X
    (Modules.dualMap C.f) P₂ P₁

/-- The short-complex bundle map is the map induced by `Modules.dualMap C.f`. -/
theorem embedding_def :
    embedding X C P₁ P₂ =
      _root_.AlgebraicGeometry.Scheme.AssociatedVectorBundle.map X
        (Modules.dualMap C.f) P₂ P₁ := sorry

/-- The short-complex bundle map, regarded as a morphism over `S`. -/
noncomputable def embeddingOver :
    over X (Modules.dual C.X₁) P₁ ⟶ over X (Modules.dual C.X₂) P₂ :=
  _root_.AlgebraicGeometry.Scheme.AssociatedVectorBundle.mapOver X
    (Modules.dualMap C.f) P₂ P₁

/-- The underlying scheme morphism of `embeddingOver` is `embedding`. -/
theorem embeddingOver_left :
    (embeddingOver X C P₁ P₂).left = embedding X C P₁ P₂ := sorry

/-- A short exact sequence of finite locally free modules induces a closed immersion of
associated vector bundles. -/
theorem embedding_isClosedImmersion (hC : C.ShortExact) [C.X₃.IsFiniteLocallyFree] :
    IsClosedImmersion (embedding X C P₁ P₂) := sorry

/-- The induced morphism over `S` is proper because its underlying bundle map is a closed
immersion. -/
theorem embedding_isProper (hC : C.ShortExact) [C.X₃.IsFiniteLocallyFree] :
    IsProper (embeddingOver X C P₁ P₂).left := sorry

end ShortExact

end AssociatedVectorBundle

end AlgebraicGeometry.Scheme

