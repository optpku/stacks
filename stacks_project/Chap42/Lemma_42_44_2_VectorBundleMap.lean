module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Symmetric.Lift
public import stacks_project.Chap42.Definition_42_29_1_Pushforward
public import stacks_project.Chap42.Lemma_42_36_3_VectorBundle
public import stacks_project.Chap42.Remark_42_33_5_Bivariant

/-!
# Maps of associated vector bundles

This file constructs the contravariant map of relative-spectrum models induced by a map of
quasi-coherent modules, and specializes it to the subbundle map associated to a short exact
sequence of finite locally free modules.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The dual of a finite locally free module of rank `r` is finite locally free of rank `r`. -/
instance instIsFiniteLocallyFreeOfRankDual {X : Scheme.{u}} (E : X.Modules) (r : ℕ)
    [IsFiniteLocallyFreeOfRank r E] :
    IsFiniteLocallyFreeOfRank r (dual E) := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.SymmetricAlgebra

variable {X : Scheme.{u}} {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]

/-- The symmetric-algebra morphism induced by a morphism of quasi-coherent modules. -/
noncomputable def map (f : F ⟶ G) : qcAlgebra F ⟶ qcAlgebra G :=
  lift F (qcAlgebra G) (f ≫ ι G)

/-- The symmetric-algebra map agrees with the original module map on degree-one generators. -/
theorem map_ι (f : F ⟶ G) :
    ι F ≫ QcAlgebraUnder.underlyingModuleMap X (map f) = f ≫ ι G := sorry

end AlgebraicGeometry.Scheme.SymmetricAlgebra

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {A B : X.QcAlgebraUnder}

/-- The contravariant morphism of chosen relative spectra induced by an algebra morphism. -/
noncomputable def relativeSpecMap (f : A ⟶ B)
    (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (Q : RelativeSpectrumOver B) [IsRelativeSpectrumOver Q] :
    relativeSpec Q ⟶ relativeSpec P :=
  (IsRelativeSpectrumOver.isRepresentedBy (P := P)).representableBy.homEquiv.symm
    (⟨relativeSpecπ Q,
      (QcAlgebraUnder.forget X).map f ≫ relativeSpecUniversalFamily Q⟩ :
      relativeSpectrumPair A (relativeSpec Q))

/-- Pulling back the universal point along `relativeSpecMap` gives the point obtained by
precomposing the source universal family with the algebra morphism. -/
theorem relativeSpecMap_spec (f : A ⟶ B)
    (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (Q : RelativeSpectrumOver B) [IsRelativeSpectrumOver Q] :
    relativeSpectrumPairPullbackMap A (relativeSpecMap f P Q) (relativeSpecPoint P) =
      (⟨relativeSpecπ Q,
        (QcAlgebraUnder.forget X).map f ≫ relativeSpecUniversalFamily Q⟩ :
        relativeSpectrumPair A (relativeSpec Q)) := sorry

/-- The relative-spectrum morphism induced by an algebra map lies over the base scheme. -/
theorem relativeSpecMap_projection (f : A ⟶ B)
    (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (Q : RelativeSpectrumOver B) [IsRelativeSpectrumOver Q] :
    relativeSpecMap f P Q ≫ relativeSpecπ P = relativeSpecπ Q := sorry

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

/-- A finite locally free associated vector bundle is locally of finite type over `S`. -/
instance over_locallyOfFiniteType [LocallyOfFiniteType X.hom]
    (F : X.left.Modules) [F.IsFiniteLocallyFree]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra F))
    [IsRelativeSpectrumOver P] : LocallyOfFiniteType (over X F P).hom :=
  _root_.AlgebraicGeometry.Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp X F P

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

/-- The projection of a finite locally free associated vector bundle is flat. -/
instance projectionOver_flat (F : X.left.Modules) [F.IsFiniteLocallyFree]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra F))
    [IsRelativeSpectrumOver P] : Flat (projectionOver X F P).left :=
  _root_.AlgebraicGeometry.Scheme.AssociatedVectorBundle.overHomFlat X F P

/-- The projection of a rank-`r` associated vector bundle has relative dimension `r`. -/
instance projectionOver_relativeDimension (F : X.left.Modules) (r : ℕ)
    [F.IsFiniteLocallyFreeOfRank r]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra F))
    [IsRelativeSpectrumOver P] : Hom.RelativeDimension (projectionOver X F P).left r :=
  _root_.AlgebraicGeometry.Scheme.AssociatedVectorBundle.overHomRelativeDimension X F r P

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

namespace AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.ShortExact

open Scheme.AssociatedVectorBundle

/-- Proper Chow pushforward along the bundle embedding induced by a short exact sequence. -/
noncomputable def pushforward
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] (C : ShortComplex X.left.Modules)
    (hC : C.ShortExact) (r₁ r₃ : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r₁ C.X₁]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (r₁ + r₃) C.X₂]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r₃ C.X₃]
    (P₁ : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra (Scheme.Modules.dual C.X₁)))
    [Scheme.IsRelativeSpectrumOver P₁]
    (P₂ : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra (Scheme.Modules.dual C.X₂)))
    [Scheme.IsRelativeSpectrumOver P₂] (n : ℤ) :
    RelativeChow delta (over X (Scheme.Modules.dual C.X₁) P₁) n →+
      RelativeChow delta (over X (Scheme.Modules.dual C.X₂) P₂) n :=
  @ChowGroup.map S inferInstance delta inferInstance
    (over X (Scheme.Modules.dual C.X₁) P₁)
    (over X (Scheme.Modules.dual C.X₂) P₂) inferInstance inferInstance
    (Scheme.AssociatedVectorBundle.ShortExact.embeddingOver X C P₁ P₂)
    (Scheme.AssociatedVectorBundle.ShortExact.embedding_isProper X C P₁ P₂ hC) n

/-- `pushforward` is the proper Chow pushforward along `embeddingOver`. -/
theorem pushforward_def
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] (C : ShortComplex X.left.Modules)
    (hC : C.ShortExact) (r₁ r₃ : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r₁ C.X₁]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (r₁ + r₃) C.X₂]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r₃ C.X₃]
    (P₁ : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra (Scheme.Modules.dual C.X₁)))
    [Scheme.IsRelativeSpectrumOver P₁]
    (P₂ : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra (Scheme.Modules.dual C.X₂)))
    [Scheme.IsRelativeSpectrumOver P₂] (n : ℤ) :
    pushforward delta X C hC r₁ r₃ P₁ P₂ n =
      @ChowGroup.map S inferInstance delta inferInstance
        (over X (Scheme.Modules.dual C.X₁) P₁)
        (over X (Scheme.Modules.dual C.X₂) P₂) inferInstance inferInstance
        (Scheme.AssociatedVectorBundle.ShortExact.embeddingOver X C P₁ P₂)
        (Scheme.AssociatedVectorBundle.ShortExact.embedding_isProper X C P₁ P₂ hC) n := sorry

end AlgebraicGeometry.ChowGroup.AssociatedVectorBundle.ShortExact
