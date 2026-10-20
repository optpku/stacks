module

public import ReasLib.AlgebraicGeometry.BivariantClass.VectorBundle
public import ReasLib.AlgebraicGeometry.BivariantClass.ProperPushforward
public import ReasLib.AlgebraicGeometry.BivariantClass.GysinAtInfinity
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.VirtualNormalBundle.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Symmetric.Map
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.ChosenMap
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.NormalCone.Comparison

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

namespace ClosedDeformation

/-- The restriction of a closed immersion to one rank locus of its virtual normal bundle. -/
noncomputable def rankHom {S Z X : Scheme.{u}}
    (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X) (hi : i ≫ p = q)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    BivariantClass.ComponentRestriction.over (Over.mk q) (@rankOpen Z X i h_i V r) ⟶
      BivariantClass.ComponentRestriction.over (Over.mk p) ⊤ :=
  BivariantClass.ComponentRestriction.hom (overHom q p i hi) (@rankOpen Z X i h_i V r) ⊤
    (rankOpen_le_preimage_top q p i hi V r)

/-- The rank restriction commutes with the canonical open inclusions. -/
theorem rankHom_commSq {S Z X : Scheme.{u}}
    (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X) (hi : i ≫ p = q)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    CommSq
      (BivariantClass.ComponentRestriction.ι (Over.mk q) (@rankOpen Z X i (inferInstance : IsImmersion i) V r)).left
      (rankHom q p i hi V r).left i
      (BivariantClass.ComponentRestriction.ι (Over.mk p) (⊤ : X.Opens)).left :=
  ⟨(Scheme.Hom.resLE_comp_ι i (rankOpen_le_preimage_top q p i hi V r)).symm⟩

/-- The morphism restricted to a virtual-normal rank locus is again an immersion. -/
theorem rankHom_isImmersion {S Z X : Scheme.{u}}
    (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X) (hi : i ≫ p = q)
    [IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    IsImmersion (rankHom q p i hi V r).left := by
  change IsImmersion (i.resLE ⊤ (@rankOpen Z X i (inferInstance : IsImmersion i) V r) _)
  infer_instance

/-- The restriction of the virtual-normal module to its rank-`r` locus. -/
abbrev rankModule {Z X : Scheme.{u}} (i : Z ⟶ X) [h_i : IsImmersion i]
    (V : VirtualNormalBundle i) (r : ℕ) : (@rankOpen Z X i h_i V r).toScheme.Modules :=
  (Scheme.Modules.pullback
    (BivariantClass.ComponentRestriction.ι (Over.mk (𝟙 Z)) (@rankOpen Z X i h_i V r)).left).obj
      V.module

/-- The module restricted to a virtual-normal rank locus is quasicoherent. -/
theorem rankModule_isQuasicoherent {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    SheafOfModules.IsQuasicoherent (rankModule i V r) := sorry

/-- The dual of the restricted virtual-normal module is quasicoherent. -/
theorem rankDualModule_isQuasicoherent {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    SheafOfModules.IsQuasicoherent (Scheme.Modules.dual (rankModule i V r)) := sorry

/-- The dual of the restricted virtual-normal module has the same constant rank. -/
theorem rankDualModule_isFiniteLocallyFreeOfRank {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Modules.dual (rankModule i V r)) :=
  sorry

/-- The quotient map on a rank locus is obtained by restricting `V.map` and applying
conormal base change. -/
noncomputable def rankQuotientMap {S Z X : Scheme.{u}}
    (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X) (hi : i ≫ p = q)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    Scheme.Modules.dual (rankModule i V r) ⟶
      Scheme.Hom.conormalSheaf (rankHom q p i hi V r).left :=
  (Scheme.Modules.pullbackDualIso
    (BivariantClass.ComponentRestriction.ι (Over.mk q) (@rankOpen Z X i (inferInstance : IsImmersion i) V r)).left
    V.module V.isFiniteLocallyFree).inv ≫
    (Scheme.Modules.pullback
      (BivariantClass.ComponentRestriction.ι (Over.mk q) (@rankOpen Z X i (inferInstance : IsImmersion i) V r)).left).map V.map ≫
    Scheme.Hom.Conormal.map (rankHom_commSq q p i hi V r)

/-- The conormal sheaf of the rankwise restricted immersion is quasicoherent. -/
theorem rankConormal_isQuasicoherent {S Z X : Scheme.{u}}
    (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X) (hi : i ≫ p = q)
    [IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    SheafOfModules.IsQuasicoherent
      (Scheme.Hom.conormalSheaf (rankHom q p i hi V r).left) := sorry

/-- The algebra morphism defining the rankwise cone-to-normal map: apply the symmetric
algebra functor to the restricted quotient `V.map`, then map to the total conormal algebra. -/
noncomputable def rankNormalAlgebraMap {S Z X : Scheme.{u}}
    (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X) (hi : i ≫ p = q)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    @Scheme.SymmetricAlgebra.qcAlgebra _ (Scheme.Modules.dual (ClosedDeformation.rankModule i V r))
      (ClosedDeformation.rankDualModule_isQuasicoherent i V r) ⟶
      @Scheme.ConormalAlgebra.total _ _ (rankHom q p i hi V r).left
        (rankHom_isImmersion q p i hi V r) :=
  @Scheme.SymmetricAlgebra.map _ _ _
      (rankDualModule_isQuasicoherent i V r)
      (rankConormal_isQuasicoherent q p i hi V r)
      (rankQuotientMap q p i hi V r) ≫
    @Scheme.ConormalAlgebra.symmetricToTotal _ _ (rankHom q p i hi V r).left
      (rankHom_isImmersion q p i hi V r)

/-- The associated vector-bundle total space over a virtual-normal rank locus. -/
noncomputable def normalOver {S Z X : Scheme.{u}} (q : Z ⟶ S) (i : Z ⟶ X)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ)
    (P : Scheme.RelativeSpectrumOver
      (@Scheme.SymmetricAlgebra.qcAlgebra _ (Scheme.Modules.dual (ClosedDeformation.rankModule i V r))
      (ClosedDeformation.rankDualModule_isQuasicoherent i V r)))
    [Scheme.IsRelativeSpectrumOver P] : Over S :=
  Over.mk (@Scheme.associatedVectorBundleπ _ (Scheme.Modules.dual (rankModule i V r))
      (rankDualModule_isQuasicoherent i V r) P inferInstance ≫
    (BivariantClass.ComponentRestriction.over (Over.mk q) (@rankOpen Z X i h_i V r)).hom)

/-- The associated vector-bundle projection over `S` on a rank locus. -/
noncomputable def normalProjection {S Z X : Scheme.{u}} (q : Z ⟶ S) (i : Z ⟶ X)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ)
    (P : Scheme.RelativeSpectrumOver
      (@Scheme.SymmetricAlgebra.qcAlgebra _ (Scheme.Modules.dual (ClosedDeformation.rankModule i V r))
      (ClosedDeformation.rankDualModule_isQuasicoherent i V r)))
    [Scheme.IsRelativeSpectrumOver P] :
    normalOver q i V r P ⟶
      BivariantClass.ComponentRestriction.over (Over.mk q) (@rankOpen Z X i h_i V r) :=
  Over.homMk (@Scheme.associatedVectorBundleπ _ (Scheme.Modules.dual (rankModule i V r))
      (rankDualModule_isQuasicoherent i V r) P inferInstance)

/-- The underlying map of `normalProjection` is the associated vector-bundle projection. -/
theorem normalProjection_left {S Z X : Scheme.{u}} (q : Z ⟶ S) (i : Z ⟶ X)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ)
    (P : Scheme.RelativeSpectrumOver
      (@Scheme.SymmetricAlgebra.qcAlgebra _ (Scheme.Modules.dual (ClosedDeformation.rankModule i V r))
      (ClosedDeformation.rankDualModule_isQuasicoherent i V r)))
    [Scheme.IsRelativeSpectrumOver P] :
    (normalProjection q i V r P).left =
      @Scheme.associatedVectorBundleπ _ (Scheme.Modules.dual (rankModule i V r))
      (rankDualModule_isQuasicoherent i V r) P inferInstance := rfl

/-- The part of the actual normal cone lying over the rank-`r` locus. -/
noncomputable def rankNormalCone {Z X : Scheme.{u}} (i : Z ⟶ X) [h_i : IsImmersion i]
    (V : VirtualNormalBundle i) (r : ℕ)
    (P : Scheme.RelativeSpectrumOver (Scheme.ConormalAlgebra.total i))
    [Scheme.IsRelativeSpectrumOver P] : Scheme.{u} :=
  Limits.pullback (Scheme.normalConeπ i P)
    (Scheme.Opens.ι (@rankOpen Z X i h_i V r))

/-- The canonical embedding of a rankwise normal cone into the fibre at infinity, obtained
from the pullback projection and the normal-cone embedding. -/
noncomputable def rankNormalConeEmbedding
    {S Z X W : Scheme.{u}} (p : X ⟶ S) (i : Z ⟶ X) [h_i : IsImmersion i]
    (V : VirtualNormalBundle i) (r : ℕ)
    (P : Scheme.RelativeSpectrumOver (Scheme.ConormalAlgebra.total i))
    [Scheme.IsRelativeSpectrumOver P]
    (b : W ⟶ ProjectiveLineFamily.space (Over.mk p))
    (e : Scheme.normalCone i P ⟶
      (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) b).left) :
    rankNormalCone i V r P ⟶
      (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) b).left :=
  pullback.fst (Scheme.normalConeπ i P)
      (Scheme.Opens.ι (@rankOpen Z X i h_i V r)) ≫ e

end ClosedDeformation

/-- Deformation to the normal cone of a closed immersion with a virtual normal bundle,
including the blowup and the quotient-induced map from the normal cone to the normal bundle. -/
structure ClosedDeformation
    {S Z X : Scheme.{u}} (q : Z ⟶ S) (p : X ⟶ S)
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (V : VirtualNormalBundle i) : Type (u + 1) where
  /-- The chosen blowup deformation space. -/
  deformationSpace : Scheme.{u}
  /-- The proper deformation morphism. -/
  deformationMap : deformationSpace ⟶ ProjectiveLineFamily.space (Over.mk p)
  /-- The deformation morphism is the blowup of `X ×ₛ ℙ¹ₛ` in the canonical closed
  subscheme `Z × {∞}`. -/
  deformationIsBlowup : IsBlowup deformationMap
    (i ≫ ProjectiveLineFamily.infinitySection (Over.mk p)).ker
  /-- Properness of the deformation morphism. -/
  deformationProper : IsProper deformationMap
  /-- The deformation is an isomorphism over the affine-line part. -/
  deformationAffineIso :
    IsIso (deformationMap ∣_ BivariantClass.GysinAtInfinity.affinePart (Over.mk p))
  /-- A relative-spectrum model of the normal bundle on every rank locus. -/
  normalModel : (r : ℕ) → Scheme.RelativeSpectrumOver
    (@Scheme.SymmetricAlgebra.qcAlgebra _ (Scheme.Modules.dual (ClosedDeformation.rankModule i V r))
      (ClosedDeformation.rankDualModule_isQuasicoherent i V r))
  /-- Each chosen normal-bundle model represents its relative spectrum. -/
  normalModelSpec : (r : ℕ) → Scheme.IsRelativeSpectrumOver (normalModel r)
  /-- A relative-spectrum model of the actual normal cone `C(Z/X)`. -/
  normalConeModel : Scheme.RelativeSpectrumOver (Scheme.ConormalAlgebra.total i)
  /-- The chosen normal-cone model represents the total conormal algebra. -/
  normalConeModelSpec : Scheme.IsRelativeSpectrumOver normalConeModel
  /-- The canonical open immersion of the actual normal cone into the fibre at infinity of
  the deformation-to-the-normal-cone blowup. -/
  normalConeEmbedding :
    @Scheme.normalCone X Z i (IsImmersion.instOfIsClosedImmersion i)
        normalConeModel normalConeModelSpec ⟶
      (BivariantClass.GysinAtInfinity.infinityFiber
        (Over.mk p) deformationMap).left
  /-- The canonical normal-cone map is an open immersion. -/
  normalConeEmbeddingOpen : IsOpenImmersion normalConeEmbedding
  /-- The normal-cone embedding respects the maps to `X`. -/
  normalConeEmbedding_over : normalConeEmbedding ≫
      (BivariantClass.GysinAtInfinity.infinityToX
        (Over.mk p) deformationMap).left =
    @Scheme.normalConeπ X Z i (IsImmersion.instOfIsClosedImmersion i)
        normalConeModel normalConeModelSpec ≫ i
  /-- The canonical embedding of each rankwise part of the actual normal cone is open. -/
  rankNormalConeEmbeddingOpen : (r : ℕ) → IsOpenImmersion
    (@ClosedDeformation.rankNormalConeEmbedding S Z X deformationSpace p i
      (IsImmersion.instOfIsClosedImmersion i) V r normalConeModel normalConeModelSpec
      deformationMap normalConeEmbedding)
  /-- The actual normal cone, represented as an open of the
  fibre at infinity rank locus by rank locus. -/
  coneOpen : (r : ℕ) →
    (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) deformationMap).left.Opens
  /-- The rank-`r` cone open is exactly the image of the actual normal cone over the rank
  locus of the virtual normal bundle. -/
  coneOpen_eq : (r : ℕ) → coneOpen r =
    @Scheme.Hom.opensRange _ _
      (@ClosedDeformation.rankNormalConeEmbedding S Z X deformationSpace p i
        (IsImmersion.instOfIsClosedImmersion i) V r normalConeModel normalConeModelSpec
        deformationMap normalConeEmbedding) (rankNormalConeEmbeddingOpen r)
  /-- Each normal-cone open maps into the top open of `X`. -/
  coneOpen_le : (r : ℕ) → coneOpen r ≤
    (BivariantClass.GysinAtInfinity.infinityToX (Over.mk p) deformationMap).left ⁻¹ᵁ
      (⊤ : X.Opens)
  /-- A relative-spectrum model of the actual normal cone after restriction to the rank
  locus. -/
  rankNormalConeModel : (r : ℕ) → Scheme.RelativeSpectrumOver
    (@Scheme.ConormalAlgebra.total _ _ (ClosedDeformation.rankHom q p i hi V r).left
      (ClosedDeformation.rankHom_isImmersion q p i hi V r))
  /-- Each rankwise normal-cone model represents the total conormal algebra. -/
  rankNormalConeModelSpec : (r : ℕ) →
    Scheme.IsRelativeSpectrumOver (rankNormalConeModel r)
  /-- The cone open in the deformation fibre is identified with the corresponding
  rankwise normal cone. -/
  rankNormalConeIso : (r : ℕ) →
    (BivariantClass.ComponentRestriction.over
      (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) deformationMap)
      (coneOpen r)).left ≅
        @Scheme.normalCone _ _ (ClosedDeformation.rankHom q p i hi V r).left
          (ClosedDeformation.rankHom_isImmersion q p i hi V r)
          (rankNormalConeModel r) (rankNormalConeModelSpec r)
  /-- The closed map from the normal cone to the chosen normal-bundle model. -/
  coneToNormal : (r : ℕ) →
    BivariantClass.ComponentRestriction.over
        (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) deformationMap)
        (coneOpen r) ⟶
      @ClosedDeformation.normalOver S Z X q i _ V r (normalModel r) (normalModelSpec r)
  /-- The cone-to-normal map is exactly the relative-spectrum morphism induced by the
  restricted quotient `V.map`, followed by the symmetric-to-total conormal algebra map. -/
  coneToNormal_eq_relativeSpecMap : (r : ℕ) → (coneToNormal r).left =
    (rankNormalConeIso r).hom ≫
      @Scheme.relativeSpecMap _ _ _
        (ClosedDeformation.rankNormalAlgebraMap q p i hi V r)
        (normalModel r) (normalModelSpec r)
        (rankNormalConeModel r) (rankNormalConeModelSpec r)
  /-- The comparison from the normal cone to the normal bundle is a closed immersion. -/
  coneToNormalClosed : (r : ℕ) → IsClosedImmersion (coneToNormal r).left
  /-- The cone-to-normal comparison respects the maps to `X`. -/
  coneToNormal_over : (r : ℕ) →
    coneToNormal r ≫
        (@ClosedDeformation.normalProjection S Z X q i _ V r (normalModel r) (normalModelSpec r) ≫
          ClosedDeformation.rankHom q p i hi V r) =
      BivariantClass.ComponentRestriction.hom
        (BivariantClass.GysinAtInfinity.infinityToX (Over.mk p) deformationMap)
        (coneOpen r) ⊤ (coneOpen_le r)

namespace ClosedDeformation

/-- Construct explicit specialization input from its deformation, normal-bundle, and
normal-cone comparison data. -/
def ofGysinAtInfinity
    {S Z X : Scheme.{u}} (q : Z ⟶ S) (p : X ⟶ S)
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (V : VirtualNormalBundle i) (W : Scheme.{u})
    (b : W ⟶ ProjectiveLineFamily.space (Over.mk p))
    (hblowup : IsBlowup b
      (i ≫ ProjectiveLineFamily.infinitySection (Over.mk p)).ker)
    (hproper : IsProper b)
    (haffine : IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart (Over.mk p)))
    (P : (r : ℕ) → Scheme.RelativeSpectrumOver
      (@Scheme.SymmetricAlgebra.qcAlgebra _ (Scheme.Modules.dual (ClosedDeformation.rankModule i V r))
      (ClosedDeformation.rankDualModule_isQuasicoherent i V r)))
    (hP : (r : ℕ) → Scheme.IsRelativeSpectrumOver (P r))
    (PC : Scheme.RelativeSpectrumOver (Scheme.ConormalAlgebra.total i))
    (hPC : Scheme.IsRelativeSpectrumOver PC)
    (eC : @Scheme.normalCone X Z i (IsImmersion.instOfIsClosedImmersion i) PC hPC ⟶
      (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) b).left)
    (heC_open : IsOpenImmersion eC)
    (heC_over : eC ≫
        (BivariantClass.GysinAtInfinity.infinityToX (Over.mk p) b).left =
      @Scheme.normalConeπ X Z i (IsImmersion.instOfIsClosedImmersion i) PC hPC ≫ i)
    (heC_rankOpen : (r : ℕ) → IsOpenImmersion
      (@rankNormalConeEmbedding S Z X W p i (IsImmersion.instOfIsClosedImmersion i)
        V r PC hPC b eC))
    (U : (r : ℕ) → (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) b).left.Opens)
    (hU_eq : (r : ℕ) → U r = @Scheme.Hom.opensRange _ _
      (@rankNormalConeEmbedding S Z X W p i (IsImmersion.instOfIsClosedImmersion i)
        V r PC hPC b eC) (heC_rankOpen r))
    (hU : (r : ℕ) → U r ≤
      (BivariantClass.GysinAtInfinity.infinityToX (Over.mk p) b).left ⁻¹ᵁ (⊤ : X.Opens))
    (PRC : (r : ℕ) → Scheme.RelativeSpectrumOver
      (@Scheme.ConormalAlgebra.total _ _ (rankHom q p i hi V r).left
        (rankHom_isImmersion q p i hi V r)))
    (hPRC : (r : ℕ) → Scheme.IsRelativeSpectrumOver (PRC r))
    (eRC : (r : ℕ) →
      (BivariantClass.ComponentRestriction.over
        (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) b) (U r)).left ≅
          @Scheme.normalCone _ _ (rankHom q p i hi V r).left
            (rankHom_isImmersion q p i hi V r) (PRC r) (hPRC r))
    (k : (r : ℕ) → BivariantClass.ComponentRestriction.over
        (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) b) (U r) ⟶
      @normalOver S Z X q i _ V r (P r) (hP r))
    (hk_eq : (r : ℕ) → (k r).left = (eRC r).hom ≫
      @Scheme.relativeSpecMap _ _ _
        (rankNormalAlgebraMap q p i hi V r)
        (P r) (hP r) (PRC r) (hPRC r))
    (hk_closed : (r : ℕ) → IsClosedImmersion (k r).left)
    (hk_over : (r : ℕ) → k r ≫
        (@normalProjection S Z X q i _ V r (P r) (hP r) ≫ rankHom q p i hi V r) =
      BivariantClass.ComponentRestriction.hom
        (BivariantClass.GysinAtInfinity.infinityToX (Over.mk p) b) (U r) ⊤ (hU r)) :
    ClosedDeformation q p i hi V where
  deformationSpace := W
  deformationMap := b
  deformationIsBlowup := hblowup
  deformationProper := hproper
  deformationAffineIso := haffine
  normalModel := P
  normalModelSpec := hP
  normalConeModel := PC
  normalConeModelSpec := hPC
  normalConeEmbedding := eC
  normalConeEmbeddingOpen := heC_open
  normalConeEmbedding_over := heC_over
  rankNormalConeEmbeddingOpen := heC_rankOpen
  coneOpen := U
  coneOpen_eq := hU_eq
  coneOpen_le := hU
  rankNormalConeModel := PRC
  rankNormalConeModelSpec := hPRC
  rankNormalConeIso := eRC
  coneToNormal := k
  coneToNormal_eq_relativeSpecMap := hk_eq
  coneToNormalClosed := hk_closed
  coneToNormal_over := hk_over

/-- The properness, affine-triviality, and closed-comparison conditions carried by a
specialization model. -/
theorem spec
    {S Z X : Scheme.{u}} (q : Z ⟶ S) (p : X ⟶ S)
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V) :
    IsBlowup D.deformationMap
        (i ≫ ProjectiveLineFamily.infinitySection (Over.mk p)).ker ∧
      IsProper D.deformationMap ∧
      IsIso (D.deformationMap ∣_
        BivariantClass.GysinAtInfinity.affinePart (Over.mk p)) ∧
      IsOpenImmersion D.normalConeEmbedding ∧
      ∀ r, D.coneOpen r =
          @Scheme.Hom.opensRange _ _
            (@rankNormalConeEmbedding S Z X D.deformationSpace p i
              (IsImmersion.instOfIsClosedImmersion i) V r D.normalConeModel
              D.normalConeModelSpec D.deformationMap D.normalConeEmbedding)
            (D.rankNormalConeEmbeddingOpen r) ∧
        IsClosedImmersion (D.coneToNormal r).left ∧
        (D.coneToNormal r).left = (D.rankNormalConeIso r).hom ≫
          @Scheme.relativeSpecMap _ _ _ (rankNormalAlgebraMap q p i hi V r)
            (D.normalModel r) (D.normalModelSpec r)
            (D.rankNormalConeModel r) (D.rankNormalConeModelSpec r) := by
  exact ⟨D.deformationIsBlowup, D.deformationProper, D.deformationAffineIso,
    D.normalConeEmbeddingOpen, fun r ↦ ⟨D.coneOpen_eq r, D.coneToNormalClosed r,
      D.coneToNormal_eq_relativeSpecMap r⟩⟩

/-- The homogeneous bivariant-class group on one virtual-normal rank locus. -/
abbrev RankClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (r : ℕ) (n : ℤ) : Type (u + 1) :=
  BivariantClass delta (rankHom q p i hi V r) n

/-- The degree-zero bivariant-class group on a chosen normal-bundle total space. -/
abbrev AmbientClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V) (r : ℕ) :
    Type (u + 1) :=
  @BivariantClass S _ delta _ _ _
    (@Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp S
      (BivariantClass.ComponentRestriction.over (Over.mk q) (@rankOpen Z X i (inferInstance : IsImmersion i) V r))
      inferInstance (Scheme.Modules.dual (rankModule i V r))
      (@Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank _ r _
        (rankDualModule_isFiniteLocallyFreeOfRank i V r))
      (D.normalModel r) (D.normalModelSpec r)) _
    (@normalProjection S Z X q i _ V r (D.normalModel r) (D.normalModelSpec r) ≫
      rankHom q p i hi V r) 0

/-- The canonical Gysin-at-infinity class attached to a specialization model. -/
noncomputable def gysinClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V) :
    @BivariantClass S _ delta _ _ _
      (@BivariantClass.GysinAtInfinity.infinityFiberLocallyOfFiniteType S D.deformationSpace
      (Over.mk p) inferInstance D.deformationMap D.deformationProper) _
      (BivariantClass.GysinAtInfinity.infinityToX (Over.mk p) D.deformationMap) 0 :=
  @BivariantClass.gysinAtInfinity S D.deformationSpace _ delta _ (Over.mk p) _
    D.deformationMap D.deformationProper D.deformationAffineIso

/-- The closed cone-to-normal comparison is proper. -/
theorem coneToNormal_proper
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V) (r : ℕ) :
    IsProper (D.coneToNormal r).left := by
  exact (IsFinite.iff_isProper_and_isAffineHom.mp
    ((IsClosedImmersion.iff_isFinite_and_mono (D.coneToNormal r).left).mp
      (D.coneToNormalClosed r)).1).1

set_option maxHeartbeats 2000000 in
/-- The degree-zero class on the normal-bundle total space obtained by restricting the
Gysin-at-infinity class to the cone and pushing it forward. -/
noncomputable def ambientClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V) (r : ℕ) :
    AmbientClass delta q p i hi V D r :=
  @BivariantClass.properPushforward S _ delta _ _ _ _
    (@BivariantClass.ComponentRestriction.locallyOfFiniteTypeOver S
      (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) D.deformationMap)
      (@BivariantClass.GysinAtInfinity.infinityFiberLocallyOfFiniteType S D.deformationSpace
      (Over.mk p) inferInstance D.deformationMap D.deformationProper) (D.coneOpen r))
    (@Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp S
      (BivariantClass.ComponentRestriction.over (Over.mk q) (@rankOpen Z X i (inferInstance : IsImmersion i) V r))
      inferInstance (Scheme.Modules.dual (rankModule i V r))
      (@Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank _ r _
        (rankDualModule_isFiniteLocallyFreeOfRank i V r))
      (D.normalModel r) (D.normalModelSpec r)) _
    (D.coneToNormal r) (coneToNormal_proper delta q p i hi V D r)
    (@normalProjection S Z X q i _ V r (D.normalModel r) (D.normalModelSpec r) ≫
      rankHom q p i hi V r) 0
    ((D.coneToNormal_over r).symm ▸
      @BivariantClass.ComponentRestriction.restrict S _ delta _ _ _
        (@BivariantClass.GysinAtInfinity.infinityFiberLocallyOfFiniteType S D.deformationSpace
      (Over.mk p) inferInstance D.deformationMap D.deformationProper) _
        (BivariantClass.GysinAtInfinity.infinityToX (Over.mk p) D.deformationMap) 0
        (D.coneOpen r) ⊤ (D.coneOpen_le r) (gysinClass delta q p i hi V D))

set_option maxHeartbeats 2000000 in
/-- The ambient class is the proper pushforward of the cone restriction of the
Gysin-at-infinity class. -/
theorem ambientClass_spec
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V) (r : ℕ) :
    ambientClass delta q p i hi V D r =
      @BivariantClass.properPushforward S _ delta _ _ _ _
    (@BivariantClass.ComponentRestriction.locallyOfFiniteTypeOver S
      (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) D.deformationMap)
      (@BivariantClass.GysinAtInfinity.infinityFiberLocallyOfFiniteType S D.deformationSpace
      (Over.mk p) inferInstance D.deformationMap D.deformationProper) (D.coneOpen r))
        (@Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp S
      (BivariantClass.ComponentRestriction.over (Over.mk q) (@rankOpen Z X i (inferInstance : IsImmersion i) V r))
      inferInstance (Scheme.Modules.dual (rankModule i V r))
      (@Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank _ r _
        (rankDualModule_isFiniteLocallyFreeOfRank i V r))
      (D.normalModel r) (D.normalModelSpec r)) _
        (D.coneToNormal r) (coneToNormal_proper delta q p i hi V D r)
        (@normalProjection S Z X q i _ V r (D.normalModel r) (D.normalModelSpec r) ≫
          rankHom q p i hi V r) 0
        ((D.coneToNormal_over r).symm ▸
          @BivariantClass.ComponentRestriction.restrict S _ delta _ _ _
        (@BivariantClass.GysinAtInfinity.infinityFiberLocallyOfFiniteType S D.deformationSpace
      (Over.mk p) inferInstance D.deformationMap D.deformationProper) _
            (BivariantClass.GysinAtInfinity.infinityToX (Over.mk p) D.deformationMap) 0
            (D.coneOpen r) ⊤ (D.coneOpen_le r) (gysinClass delta q p i hi V D)) := rfl

end ClosedDeformation

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

set_option maxHeartbeats 2000000 in
/-- The homogeneous degree-`r` class obtained by descending the degree-zero specialization
class through vector-bundle flat pullback. -/
noncomputable def closedClassOfRank
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V) (r : ℕ) :
    BivariantClass delta (ClosedDeformation.rankHom q p i hi V r) (r : ℤ) :=
  (@AddEquiv.toEquiv _ _ (BivariantClass.pointwiseAddCommGroup delta (ClosedDeformation.rankHom q p i hi V r) (r : ℤ)).toAdd (@BivariantClass.pointwiseAddCommGroup S _ delta _ _ _
      (@Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp S
        (BivariantClass.ComponentRestriction.over (Over.mk q) (@rankOpen Z X i (inferInstance : IsImmersion i) V r))
        inferInstance (Scheme.Modules.dual (ClosedDeformation.rankModule i V r))
        (@Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank _ r _
          (ClosedDeformation.rankDualModule_isFiniteLocallyFreeOfRank i V r))
        (D.normalModel r) (D.normalModelSpec r)) _
      (@ClosedDeformation.normalProjection S Z X q i _ V r
        (D.normalModel r) (D.normalModelSpec r) ≫
        ClosedDeformation.rankHom q p i hi V r) 0).toAdd
    (@AddEquiv.ofBijective _ _ _
    (BivariantClass.pointwiseAddCommGroup delta (ClosedDeformation.rankHom q p i hi V r) (r : ℤ)).toAdd
    (@BivariantClass.pointwiseAddCommGroup S _ delta _ _ _
      (@Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp S
        (BivariantClass.ComponentRestriction.over (Over.mk q) (@rankOpen Z X i (inferInstance : IsImmersion i) V r))
        inferInstance (Scheme.Modules.dual (ClosedDeformation.rankModule i V r))
        (@Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank _ r _
          (ClosedDeformation.rankDualModule_isFiniteLocallyFreeOfRank i V r))
        (D.normalModel r) (D.normalModelSpec r)) _
      (@ClosedDeformation.normalProjection S Z X q i _ V r
        (D.normalModel r) (D.normalModelSpec r) ≫
        ClosedDeformation.rankHom q p i hi V r) 0).toAdd inferInstance inferInstance
    (@BivariantClass.vectorBundleComposition S _ delta _ _ _ _ _
    (ClosedDeformation.rankHom q p i hi V r)
    (Scheme.Modules.dual (ClosedDeformation.rankModule i V r)) r
    (ClosedDeformation.rankDualModule_isFiniteLocallyFreeOfRank i V r)
    (D.normalModel r) (D.normalModelSpec r)) (@BivariantClass.vectorBundleComposition_bijective S _ delta _ _ _ _ _
    (ClosedDeformation.rankHom q p i hi V r)
    (Scheme.Modules.dual (ClosedDeformation.rankModule i V r)) r
    (ClosedDeformation.rankDualModule_isFiniteLocallyFreeOfRank i V r)
    (D.normalModel r) (D.normalModelSpec r)))).symm
    (ClosedDeformation.ambientClass delta q p i hi V D r)

set_option maxHeartbeats 2000000 in
/-- Pulling `closedClassOfRank` back to the normal-bundle total space recovers the
degree-zero specialization class. -/
theorem closedClassOfRank_spec
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V) (r : ℕ) :
    @BivariantClass.vectorBundleComposition S _ delta _ _ _ _ _
      (ClosedDeformation.rankHom q p i hi V r)
      (Scheme.Modules.dual (ClosedDeformation.rankModule i V r)) r
      (ClosedDeformation.rankDualModule_isFiniteLocallyFreeOfRank i V r)
      (D.normalModel r) (D.normalModelSpec r)
      (closedClassOfRank delta q p i hi V D r) =
        ClosedDeformation.ambientClass delta q p i hi V D r := by
  exact (@AddEquiv.toEquiv _ _ (BivariantClass.pointwiseAddCommGroup delta (ClosedDeformation.rankHom q p i hi V r) (r : ℤ)).toAdd (@BivariantClass.pointwiseAddCommGroup S _ delta _ _ _
      (@Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp S
        (BivariantClass.ComponentRestriction.over (Over.mk q) (@rankOpen Z X i (inferInstance : IsImmersion i) V r))
        inferInstance (Scheme.Modules.dual (ClosedDeformation.rankModule i V r))
        (@Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank _ r _
          (ClosedDeformation.rankDualModule_isFiniteLocallyFreeOfRank i V r))
        (D.normalModel r) (D.normalModelSpec r)) _
      (@ClosedDeformation.normalProjection S Z X q i _ V r
        (D.normalModel r) (D.normalModelSpec r) ≫
        ClosedDeformation.rankHom q p i hi V r) 0).toAdd
    (@AddEquiv.ofBijective _ _ _
    (BivariantClass.pointwiseAddCommGroup delta (ClosedDeformation.rankHom q p i hi V r) (r : ℤ)).toAdd
    (@BivariantClass.pointwiseAddCommGroup S _ delta _ _ _
      (@Scheme.AssociatedVectorBundle.locallyOfFiniteTypeComp S
        (BivariantClass.ComponentRestriction.over (Over.mk q) (@rankOpen Z X i (inferInstance : IsImmersion i) V r))
        inferInstance (Scheme.Modules.dual (ClosedDeformation.rankModule i V r))
        (@Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank _ r _
          (ClosedDeformation.rankDualModule_isFiniteLocallyFreeOfRank i V r))
        (D.normalModel r) (D.normalModelSpec r)) _
      (@ClosedDeformation.normalProjection S Z X q i _ V r
        (D.normalModel r) (D.normalModelSpec r) ≫
        ClosedDeformation.rankHom q p i hi V r) 0).toAdd inferInstance inferInstance
    (@BivariantClass.vectorBundleComposition S _ delta _ _ _ _ _
    (ClosedDeformation.rankHom q p i hi V r)
    (Scheme.Modules.dual (ClosedDeformation.rankModule i V r)) r
    (ClosedDeformation.rankDualModule_isFiniteLocallyFreeOfRank i V r)
    (D.normalModel r) (D.normalModelSpec r)) (@BivariantClass.vectorBundleComposition_bijective S _ delta _ _ _ _ _
    (ClosedDeformation.rankHom q p i hi V r)
    (Scheme.Modules.dual (ClosedDeformation.rankModule i V r)) r
    (ClosedDeformation.rankDualModule_isFiniteLocallyFreeOfRank i V r)
    (D.normalModel r) (D.normalModelSpec r)))).apply_symm_apply _

/-- The completed virtual-normal class, with the degree-`r` class placed on the rank-`r`
clopen locus. -/
noncomputable def closedClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V) :
    BivariantClass.OpenRestriction.Completion delta (overHom q p i hi)
      (fun r : ℕ ↦ @rankOpen Z X i
        (inferInstance : IsImmersion i) V r)
      (fun _ : Unit ↦ ⊤) (fun _ ↦ Unit.unit)
      (fun r ↦ rankOpen_le_preimage_top q p i hi V r) :=
  fun r ↦ @DirectSum.of ℕ
    (fun n : ℕ ↦ BivariantClass delta
      (ClosedDeformation.rankHom q p i hi V r) (n : ℤ))
    (fun n ↦ (BivariantClass.pointwiseAddCommGroup delta
      (ClosedDeformation.rankHom q p i hi V r) (n : ℤ)).toAddCommMonoid)
    inferInstance r
    (closedClassOfRank delta q p i hi V D r)

/-- The degree matching a rank locus is its descended homogeneous class. -/
theorem closedClass_component
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V) (r : ℕ) :
    closedClass delta q p i hi V D r r = closedClassOfRank delta q p i hi V D r := sorry

/-- Every degree other than the rank vanishes on a fixed rank locus. -/
theorem closedClass_component_ne
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V)
    (r n : ℕ) (hne : n ≠ r) : closedClass delta q p i hi V D r n =
      BivariantClass.pointwiseZero delta (ClosedDeformation.rankHom q p i hi V r) (n : ℤ) := sorry

namespace ClosedDeformation

/-- The rank-`r` locus of a pulled virtual normal bundle lies over the original rank-`r`
locus. -/
theorem rankOpen_le_baseChange_preimage
    {S Z X Z' X' : Scheme.{u}} (q : Z ⟶ S) (p : X ⟶ S)
    (q' : Z' ⟶ S) (p' : X' ⟶ S)
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (i' : Z' ⟶ X') (hi' : i' ≫ p' = q') [h_i' : IsClosedImmersion i']
    (g : Over.mk q' ⟶ Over.mk q) (f : Over.mk p' ⟶ Over.mk p)
    (square : IsPullback g.left i' i f.left)
    (V : VirtualNormalBundle i) (r : ℕ) :
    @rankOpen Z' X' i' (IsImmersion.instOfIsClosedImmersion i')
        (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
          (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
          square V) r ≤
      g.left ⁻¹ᵁ @rankOpen Z X i (IsImmersion.instOfIsClosedImmersion i) V r := sorry

/-- The canonical map between corresponding rank loci in a cartesian base change. -/
noncomputable def rankBaseChangeSource
    {S Z X Z' X' : Scheme.{u}} (q : Z ⟶ S) (p : X ⟶ S)
    (q' : Z' ⟶ S) (p' : X' ⟶ S)
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (i' : Z' ⟶ X') (hi' : i' ≫ p' = q') [h_i' : IsClosedImmersion i']
    (g : Over.mk q' ⟶ Over.mk q) (f : Over.mk p' ⟶ Over.mk p)
    (square : IsPullback g.left i' i f.left)
    (V : VirtualNormalBundle i) (r : ℕ) :
    BivariantClass.ComponentRestriction.over (Over.mk q')
        (@rankOpen Z' X' i' (IsImmersion.instOfIsClosedImmersion i')
          (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
            (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
            square V) r) ⟶
      BivariantClass.ComponentRestriction.over (Over.mk q)
        (@rankOpen Z X i (IsImmersion.instOfIsClosedImmersion i) V r) :=
  BivariantClass.ComponentRestriction.hom g
    (@rankOpen Z' X' i' (IsImmersion.instOfIsClosedImmersion i')
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) r)
    (@rankOpen Z X i (IsImmersion.instOfIsClosedImmersion i) V r)
    (rankOpen_le_baseChange_preimage q p q' p' i hi i' hi' g f square V r)

/-- The canonical map between the top-open restrictions of the two targets. -/
noncomputable def topBaseChangeTarget
    {S X X' : Scheme.{u}} (p : X ⟶ S) (p' : X' ⟶ S)
    (f : Over.mk p' ⟶ Over.mk p) :
    BivariantClass.ComponentRestriction.over (Over.mk p') ⊤ ⟶
      BivariantClass.ComponentRestriction.over (Over.mk p) ⊤ :=
  BivariantClass.ComponentRestriction.hom f ⊤ ⊤ (by simp)

/-- The canonical map between the top-open restrictions is locally of finite type. -/
instance topBaseChangeTarget_locallyOfFiniteType
    {S X X' : Scheme.{u}} (p : X ⟶ S) (p' : X' ⟶ S) [LocallyOfFiniteType p']
    (f : Over.mk p' ⟶ Over.mk p) : LocallyOfFiniteType (topBaseChangeTarget p p' f).left :=
  sorry

/-- Restricting a cartesian square to corresponding virtual-normal rank loci again gives
a cartesian square. -/
theorem rankBaseChangeSquare
    {S Z X Z' X' : Scheme.{u}} (q : Z ⟶ S) (p : X ⟶ S)
    (q' : Z' ⟶ S) (p' : X' ⟶ S)
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (i' : Z' ⟶ X') (hi' : i' ≫ p' = q') [h_i' : IsClosedImmersion i']
    (g : Over.mk q' ⟶ Over.mk q) (f : Over.mk p' ⟶ Over.mk p)
    (square : IsPullback g.left i' i f.left)
    (V : VirtualNormalBundle i) (r : ℕ) :
    IsPullback (rankBaseChangeSource q p q' p' i hi i' hi' g f square V r).left
      (@rankHom S Z' X' q' p' i' hi' (IsImmersion.instOfIsClosedImmersion i')
        (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
          (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
          square V) r).left
      (@rankHom S Z X q p i hi (IsImmersion.instOfIsClosedImmersion i) V r).left
      (topBaseChangeTarget p p' f).left := sorry



end ClosedDeformation

/-- Rankwise cartesian restriction preserves the zero bivariant class. -/
theorem rankBaseChange_map_zero
    {S Z X Z' X' : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    (q' : Z' ⟶ S) (p' : X' ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    [LocallyOfFiniteType q'] [LocallyOfFiniteType p']
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (i' : Z' ⟶ X') (hi' : i' ≫ p' = q') [h_i' : IsClosedImmersion i']
    (g : Over.mk q' ⟶ Over.mk q) (f : Over.mk p' ⟶ Over.mk p)
    (square : IsPullback g.left i' i f.left)
    (V : VirtualNormalBundle i)
    (r : ℕ) (n : ℤ) :
    (BivariantClass.restrict delta
    (ClosedDeformation.rankBaseChangeSource q p q' p' i hi i' hi' g f square V r)
    (@ClosedDeformation.rankHom S Z' X' q' p' i' hi'
      (IsImmersion.instOfIsClosedImmersion i')
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) r)
    (ClosedDeformation.topBaseChangeTarget p p' f)
    (ClosedDeformation.rankBaseChangeSquare q p q' p' i hi i' hi' g f square V r) n) (BivariantClass.pointwiseZero delta (ClosedDeformation.rankHom q p i hi V r) n) =
      BivariantClass.pointwiseZero delta (@ClosedDeformation.rankHom S Z' X' q' p' i' hi'
      (IsImmersion.instOfIsClosedImmersion i')
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) r) n := sorry

/-- Rankwise cartesian restriction preserves pointwise addition. -/
theorem rankBaseChange_map_add
    {S Z X Z' X' : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    (q' : Z' ⟶ S) (p' : X' ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    [LocallyOfFiniteType q'] [LocallyOfFiniteType p']
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (i' : Z' ⟶ X') (hi' : i' ≫ p' = q') [h_i' : IsClosedImmersion i']
    (g : Over.mk q' ⟶ Over.mk q) (f : Over.mk p' ⟶ Over.mk p)
    (square : IsPullback g.left i' i f.left)
    (V : VirtualNormalBundle i)
    (r : ℕ) (n : ℤ) (c d : ClosedDeformation.RankClass delta q p i hi V r n) :
    (BivariantClass.restrict delta
    (ClosedDeformation.rankBaseChangeSource q p q' p' i hi i' hi' g f square V r)
    (@ClosedDeformation.rankHom S Z' X' q' p' i' hi'
      (IsImmersion.instOfIsClosedImmersion i')
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) r)
    (ClosedDeformation.topBaseChangeTarget p p' f)
    (ClosedDeformation.rankBaseChangeSquare q p q' p' i hi i' hi' g f square V r) n) (BivariantClass.pointwiseAdd delta (ClosedDeformation.rankHom q p i hi V r) n c d) =
      BivariantClass.pointwiseAdd delta (@ClosedDeformation.rankHom S Z' X' q' p' i' hi'
      (IsImmersion.instOfIsClosedImmersion i')
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) r) n
        ((BivariantClass.restrict delta
    (ClosedDeformation.rankBaseChangeSource q p q' p' i hi i' hi' g f square V r)
    (@ClosedDeformation.rankHom S Z' X' q' p' i' hi'
      (IsImmersion.instOfIsClosedImmersion i')
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) r)
    (ClosedDeformation.topBaseChangeTarget p p' f)
    (ClosedDeformation.rankBaseChangeSquare q p q' p' i hi i' hi' g f square V r) n) c) ((BivariantClass.restrict delta
    (ClosedDeformation.rankBaseChangeSource q p q' p' i hi i' hi' g f square V r)
    (@ClosedDeformation.rankHom S Z' X' q' p' i' hi'
      (IsImmersion.instOfIsClosedImmersion i')
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) r)
    (ClosedDeformation.topBaseChangeTarget p p' f)
    (ClosedDeformation.rankBaseChangeSquare q p q' p' i hi i' hi' g f square V r) n) d) := sorry

/-- Additive restriction of bivariant classes to corresponding rank loci in a cartesian square. -/
def rankBaseChange
    {S Z X Z' X' : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    (q' : Z' ⟶ S) (p' : X' ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    [LocallyOfFiniteType q'] [LocallyOfFiniteType p']
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (i' : Z' ⟶ X') (hi' : i' ≫ p' = q') [h_i' : IsClosedImmersion i']
    (g : Over.mk q' ⟶ Over.mk q) (f : Over.mk p' ⟶ Over.mk p)
    (square : IsPullback g.left i' i f.left)
    (V : VirtualNormalBundle i)
    (r : ℕ) (n : ℤ) :
    @AddMonoidHom (ClosedDeformation.RankClass delta q p i hi V r n) (ClosedDeformation.RankClass delta q' p' i' hi'
        (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
          (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
          square V) r n)
      (BivariantClass.pointwiseAddCommGroup delta (ClosedDeformation.rankHom q p i hi V r) n).toAddZero (BivariantClass.pointwiseAddCommGroup delta (@ClosedDeformation.rankHom S Z' X' q' p' i' hi'
      (IsImmersion.instOfIsClosedImmersion i')
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) r) n).toAddZero :=
  @AddMonoidHom.mk _ _ (BivariantClass.pointwiseAddCommGroup delta (ClosedDeformation.rankHom q p i hi V r) n).toAddZero (BivariantClass.pointwiseAddCommGroup delta (@ClosedDeformation.rankHom S Z' X' q' p' i' hi'
      (IsImmersion.instOfIsClosedImmersion i')
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) r) n).toAddZero
    (@ZeroHom.mk _ _ (BivariantClass.pointwiseAddCommGroup delta (ClosedDeformation.rankHom q p i hi V r) n).toZero (BivariantClass.pointwiseAddCommGroup delta (@ClosedDeformation.rankHom S Z' X' q' p' i' hi'
      (IsImmersion.instOfIsClosedImmersion i')
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) r) n).toZero (BivariantClass.restrict delta
    (ClosedDeformation.rankBaseChangeSource q p q' p' i hi i' hi' g f square V r)
    (@ClosedDeformation.rankHom S Z' X' q' p' i' hi'
      (IsImmersion.instOfIsClosedImmersion i')
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) r)
    (ClosedDeformation.topBaseChangeTarget p p' f)
    (ClosedDeformation.rankBaseChangeSquare q p q' p' i hi i' hi' g f square V r) n)
    (rankBaseChange_map_zero delta q p q' p' i hi i' hi' g f square V r n))
    (rankBaseChange_map_add delta q p q' p' i hi i' hi' g f square V r n)

/-- Evaluation of `rankBaseChange` is the canonical `BivariantClass.restrict` along the
induced cartesian square of rank loci. -/
theorem rankBaseChange_apply
    {S Z X Z' X' : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    (q' : Z' ⟶ S) (p' : X' ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    [LocallyOfFiniteType q'] [LocallyOfFiniteType p']
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (i' : Z' ⟶ X') (hi' : i' ≫ p' = q') [h_i' : IsClosedImmersion i']
    (g : Over.mk q' ⟶ Over.mk q) (f : Over.mk p' ⟶ Over.mk p)
    (square : IsPullback g.left i' i f.left)
    (V : VirtualNormalBundle i)
    (r : ℕ) (n : ℤ) (c : ClosedDeformation.RankClass delta q p i hi V r n) :
    rankBaseChange delta q p q' p' i hi i' hi' g f square V r n c =
      BivariantClass.restrict delta
        (ClosedDeformation.rankBaseChangeSource q p q' p' i hi i' hi' g f square V r)
        (@ClosedDeformation.rankHom S Z' X' q' p' i' hi'
          (IsImmersion.instOfIsClosedImmersion i')
          (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
            (IsImmersion.instOfIsClosedImmersion i')
            (IsImmersion.instOfIsClosedImmersion i) square V) r)
        (ClosedDeformation.topBaseChangeTarget p p' f)
        (ClosedDeformation.rankBaseChangeSquare q p q' p' i hi i' hi' g f square V r) n c := rfl

/-- Canonical completed restriction of the closed virtual-normal class along a cartesian
base change. -/
noncomputable def closedClassBaseChange
    {S Z X Z' X' : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    (q' : Z' ⟶ S) (p' : X' ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    [LocallyOfFiniteType q'] [LocallyOfFiniteType p']
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (i' : Z' ⟶ X') (hi' : i' ≫ p' = q') [h_i' : IsClosedImmersion i']
    (g : Over.mk q' ⟶ Over.mk q) (f : Over.mk p' ⟶ Over.mk p)
    (square : IsPullback g.left i' i f.left)
    (V : VirtualNormalBundle i)
    (D : ClosedDeformation q p i hi V) :
    BivariantClass.OpenRestriction.Completion delta (overHom q' p' i' hi')
      (fun r : ℕ ↦ @rankOpen Z' X' i'
        (IsImmersion.instOfIsClosedImmersion i')
        (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
          (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
          square V) r)
      (fun _ : Unit ↦ ⊤) (fun _ ↦ Unit.unit)
      (fun r ↦ rankOpen_le_preimage_top q' p' i' hi'
        (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
          (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
          square V) r) :=
  fun r ↦ @DirectSum.map ℕ _ _
      (fun n ↦ (BivariantClass.pointwiseAddCommGroup delta
        (ClosedDeformation.rankHom q p i hi V r) (n : ℤ)).toAddCommMonoid)
      (fun n ↦ (BivariantClass.pointwiseAddCommGroup delta
        (@ClosedDeformation.rankHom S Z' X' q' p' i' hi'
      (IsImmersion.instOfIsClosedImmersion i')
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) r) (n : ℤ)).toAddCommMonoid)
      (fun n : ℕ ↦
    rankBaseChange delta q p q' p' i hi i' hi' g f square V r (n : ℤ))
      (closedClass delta q p i hi V D r)

/-- Each component of completed base change is induced by canonical bivariant
restriction on the corresponding rank locus. -/
theorem closedClassBaseChange_component
    {S Z X Z' X' : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    (q' : Z' ⟶ S) (p' : X' ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    [LocallyOfFiniteType q'] [LocallyOfFiniteType p']
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (i' : Z' ⟶ X') (hi' : i' ≫ p' = q') [h_i' : IsClosedImmersion i']
    (g : Over.mk q' ⟶ Over.mk q) (f : Over.mk p' ⟶ Over.mk p)
    (square : IsPullback g.left i' i f.left)
    (V : VirtualNormalBundle i)
    (D : ClosedDeformation q p i hi V) (r : ℕ) :
    closedClassBaseChange delta q p q' p' i hi i' hi' g f square V D r =
      @DirectSum.map ℕ _ _
      (fun n ↦ (BivariantClass.pointwiseAddCommGroup delta
        (ClosedDeformation.rankHom q p i hi V r) (n : ℤ)).toAddCommMonoid)
      (fun n ↦ (BivariantClass.pointwiseAddCommGroup delta
        (@ClosedDeformation.rankHom S Z' X' q' p' i' hi'
      (IsImmersion.instOfIsClosedImmersion i')
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) r) (n : ℤ)).toAddCommMonoid)
      (fun n : ℕ ↦
        rankBaseChange delta q p q' p' i hi i' hi' g f square V r (n : ℤ))
          (closedClass delta q p i hi V D r) := rfl

/-- The completed closed class of the pulled virtual normal bundle is the canonical bivariant
restriction of the original completed class. -/
theorem closedClass_pullback
    {S Z X Z' X' : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    (q' : Z' ⟶ S) (p' : X' ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    [LocallyOfFiniteType q'] [LocallyOfFiniteType p']
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (i' : Z' ⟶ X') (hi' : i' ≫ p' = q') [h_i' : IsClosedImmersion i']
    (g : Over.mk q' ⟶ Over.mk q) (f : Over.mk p' ⟶ Over.mk p)
    (square : IsPullback g.left i' i f.left)
    (V : VirtualNormalBundle i)
    (D : ClosedDeformation q p i hi V)
    (D' : ClosedDeformation q' p' i' hi'
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V)) :
    closedClass delta q' p' i' hi'
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) D' =
      closedClassBaseChange delta q p q' p' i hi i' hi' g f square V D := sorry

/-- The global degree-`r` class obtained by gluing the completed rank-locus components. -/
noncomputable def globalClassOfRank
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V) (r : ℕ) :
    BivariantClass delta (overHom q p i hi) (r : ℤ) :=
  ((BivariantClass.OpenRestriction.Completion.globalEquiv delta
    (overHom q p i hi) (fun n : ℕ ↦ @rankOpen
      Z X i (inferInstance : IsImmersion i) V n) (fun _ : Unit ↦ ⊤)
    (fun _ ↦ Unit.unit) ((@Scheme.Modules.rankClopen_iSup Z V.module V.isFiniteLocallyFree))
    ((by simp)) ((@Scheme.Modules.rankClopen_pairwiseDisjoint Z V.module V.isFiniteLocallyFree))
    ((by intro a b h; exact (h (Subsingleton.elim a b)).elim))
    ((fun n ↦ (@Scheme.Modules.rankClopen Z V.module V.isFiniteLocallyFree n).isClopen)) ((fun _ ↦ isClopen_univ))
    (fun n ↦ rankOpen_le_preimage_top q p i hi V n))
      (closedClass delta q p i hi V D)).1 r

/-- Restricting `globalClassOfRank` to the rank loci recovers the degree-`r` component of
the completed class. -/
theorem globalClassOfRank_component
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V) (r : ℕ) :
    globalClassOfRank delta q p i hi V D r =
      ((BivariantClass.OpenRestriction.Completion.globalEquiv delta
        (overHom q p i hi)
        (fun n : ℕ ↦ @rankOpen Z X i
          (inferInstance : IsImmersion i) V n) (fun _ : Unit ↦ ⊤)
        (fun _ ↦ Unit.unit) ((@Scheme.Modules.rankClopen_iSup Z V.module V.isFiniteLocallyFree))
        ((by simp))
        ((@Scheme.Modules.rankClopen_pairwiseDisjoint Z V.module V.isFiniteLocallyFree))
        ((by intro a b h; exact (h (Subsingleton.elim a b)).elim))
        ((fun n ↦ (@Scheme.Modules.rankClopen Z V.module V.isFiniteLocallyFree n).isClopen)) ((fun _ ↦ isClopen_univ))
        (fun n ↦ rankOpen_le_preimage_top q p i hi V n))
          (closedClass delta q p i hi V D)).1 r := rfl

/-- If the virtual normal bundle has constant rank `r`, the completed class is the
completion of its single global homogeneous degree-`r` class. -/
theorem closedClass_eq_completeOfRank
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r V.module] :
    closedClass delta q p i hi V D =
      BivariantClass.OpenRestriction.Completion.complete delta
        (overHom q p i hi)
        (fun n : ℕ ↦ @rankOpen Z X i
          (inferInstance : IsImmersion i) V n)
        (fun _ : Unit ↦ ⊤) (fun _ ↦ Unit.unit)
        (fun n ↦ rankOpen_le_preimage_top q p i hi V n)
        (@DirectSum.of ℕ
          (fun n : ℕ ↦ BivariantClass delta (overHom q p i hi) (n : ℤ))
          (fun n ↦ (BivariantClass.pointwiseAddCommGroup delta
            (overHom q p i hi) (n : ℤ)).toAddCommMonoid)
          inferInstance r (globalClassOfRank delta q p i hi V D r)) := sorry

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
