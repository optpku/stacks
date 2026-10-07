module

public import stacks_project.Chap42.«42_50_2_1_BivariantPushforward»
public import stacks_project.Chap42.Lemma_42_36_3
public import stacks_project.Chap42.Lemma_42_44_2_VectorBundleMap
public import stacks_project.Chap42.Lemma_42_48_1_GysinAtInfinity
public import stacks_project.Chap42.Lemma_42_48_2_BaseChange
public import stacks_project.Chap42.Lemma_42_54_1_Pullback
public import stacks_project.Chap42.Remark_42_54_11_Variant_for_immersions_Bivariant
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.NormalCone.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.FiniteLocallyFree

/-!
# The closed-immersion class of a virtual normal bundle

This file isolates the explicit deformation-to-the-normal-cone choices and constructs the
resulting completed bivariant class rank locus by rank locus.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

namespace ClosedSpecialization

/-- The restriction of a closed immersion to one rank locus of its virtual normal bundle. -/
noncomputable def rankHom {S Z X : Scheme.{u}}
    (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X) (hi : i ≫ p = q)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    BivariantClass.OpenRestriction.over (Over.mk q) (@rankOpen Z X i h_i V r) ⟶
      BivariantClass.OpenRestriction.over (Over.mk p) ⊤ :=
  BivariantClass.OpenRestriction.hom (overHom q p i hi) (@rankOpen Z X i h_i V r) ⊤
    (rankOpen_le_preimage_top q p i hi V r)

/-- `rankHom` is the canonical open restriction of the original morphism. -/
theorem rankHom_def {S Z X : Scheme.{u}}
    (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X) (hi : i ≫ p = q)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    rankHom q p i hi V r =
      BivariantClass.OpenRestriction.hom (overHom q p i hi)
        (@rankOpen Z X i h_i V r) ⊤ (rankOpen_le_preimage_top q p i hi V r) := sorry

/-- Restricting a closed immersion to a virtual-normal rank locus is a cartesian base
change along the canonical open inclusions. -/
theorem rankHom_isPullback {S Z X : Scheme.{u}}
    (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X) (hi : i ≫ p = q)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    IsPullback
      (BivariantClass.OpenRestriction.ι (Over.mk q) (@rankOpen Z X i h_i V r)).left
      (rankHom q p i hi V r).left i
      (BivariantClass.OpenRestriction.ι (Over.mk p) (⊤ : X.Opens)).left := sorry

/-- The morphism restricted to a virtual-normal rank locus is again an immersion. -/
instance rankHom_isImmersion {S Z X : Scheme.{u}}
    (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X) (hi : i ≫ p = q)
    [IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    IsImmersion (rankHom q p i hi V r).left := sorry

/-- The restriction of the virtual-normal module to its rank-`r` locus. -/
abbrev rankModule {Z X : Scheme.{u}} (i : Z ⟶ X) [h_i : IsImmersion i]
    (V : VirtualNormalBundle i) (r : ℕ) : (@rankOpen Z X i h_i V r).toScheme.Modules :=
  (Scheme.Modules.pullback
    (BivariantClass.OpenRestriction.ι (Over.mk (𝟙 Z)) (@rankOpen Z X i h_i V r)).left).obj
      V.module

/-- The restricted module used by the rankwise construction is ordinary module pullback. -/
theorem rankModule_def {Z X : Scheme.{u}} (i : Z ⟶ X) [h_i : IsImmersion i]
    (V : VirtualNormalBundle i) (r : ℕ) :
    rankModule i V r =
      (Scheme.Modules.pullback
        (BivariantClass.OpenRestriction.ι
          (Over.mk (𝟙 Z)) (@rankOpen Z X i h_i V r)).left).obj V.module := sorry

/-- The module restricted to a virtual-normal rank locus is quasicoherent. -/
instance rankModule_isQuasicoherent {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    SheafOfModules.IsQuasicoherent (rankModule i V r) := sorry

/-- The dual of the restricted virtual-normal module is quasicoherent. -/
instance rankDualModule_isQuasicoherent {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    SheafOfModules.IsQuasicoherent (Scheme.Modules.dual (rankModule i V r)) := sorry

/-- On its rank-`r` locus, the restricted virtual-normal module has constant rank `r`. -/
instance rankModule_isFiniteLocallyFreeOfRank {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank r (rankModule i V r) := sorry

/-- The dual of the restricted virtual-normal module has the same constant rank. -/
instance rankDualModule_isFiniteLocallyFreeOfRank {Z X : Scheme.{u}} (i : Z ⟶ X)
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
  @VirtualNormalBundle.pullbackMap Z X
    (BivariantClass.OpenRestriction.over (Over.mk q) (@rankOpen Z X i h_i V r)).left
    (BivariantClass.OpenRestriction.over (Over.mk p) (⊤ : X.Opens)).left
    (BivariantClass.OpenRestriction.ι (Over.mk q) (@rankOpen Z X i h_i V r)).left
    (rankHom q p i hi V r).left i
    (BivariantClass.OpenRestriction.ι (Over.mk p) (⊤ : X.Opens)).left
    (rankHom_isImmersion q p i hi V r) h_i
    (rankHom_isPullback q p i hi V r) V

/-- `rankQuotientMap` is the canonical pullback quotient map of `V`. -/
theorem rankQuotientMap_def {S Z X : Scheme.{u}}
    (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X) (hi : i ≫ p = q)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    rankQuotientMap q p i hi V r =
      @VirtualNormalBundle.pullbackMap Z X
        (BivariantClass.OpenRestriction.over
          (Over.mk q) (@rankOpen Z X i h_i V r)).left
        (BivariantClass.OpenRestriction.over (Over.mk p) (⊤ : X.Opens)).left
        (BivariantClass.OpenRestriction.ι
          (Over.mk q) (@rankOpen Z X i h_i V r)).left
        (rankHom q p i hi V r).left i
        (BivariantClass.OpenRestriction.ι (Over.mk p) (⊤ : X.Opens)).left
        (rankHom_isImmersion q p i hi V r) h_i
        (rankHom_isPullback q p i hi V r) V := sorry

/-- The conormal sheaf of the rankwise restricted immersion is quasicoherent. -/
instance rankConormal_isQuasicoherent {S Z X : Scheme.{u}}
    (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X) (hi : i ≫ p = q)
    [IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    SheafOfModules.IsQuasicoherent
      (Scheme.Hom.conormalSheaf (rankHom q p i hi V r).left) := sorry

/-- The algebra morphism defining the rankwise cone-to-normal map: apply the symmetric
algebra functor to the restricted quotient `V.map`, then map to the total conormal algebra. -/
noncomputable def rankNormalAlgebraMap {S Z X : Scheme.{u}}
    (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X) (hi : i ≫ p = q)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    Scheme.SymmetricAlgebra.qcAlgebra (Scheme.Modules.dual (rankModule i V r)) ⟶
      @Scheme.ConormalAlgebra.total _ _ (rankHom q p i hi V r).left
        (rankHom_isImmersion q p i hi V r) :=
  @Scheme.SymmetricAlgebra.map _ _ _
      (rankDualModule_isQuasicoherent i V r)
      (rankConormal_isQuasicoherent q p i hi V r)
      (rankQuotientMap q p i hi V r) ≫
    @Scheme.ConormalAlgebra.symmetricToTotal _ _ (rankHom q p i hi V r).left
      (rankHom_isImmersion q p i hi V r)

/-- `rankNormalAlgebraMap` is induced by the restricted virtual-normal quotient and the
canonical symmetric-to-total conormal map. -/
theorem rankNormalAlgebraMap_def {S Z X : Scheme.{u}}
    (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X) (hi : i ≫ p = q)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    rankNormalAlgebraMap q p i hi V r =
      @Scheme.SymmetricAlgebra.map _ _ _
          (rankDualModule_isQuasicoherent i V r)
          (rankConormal_isQuasicoherent q p i hi V r)
          (rankQuotientMap q p i hi V r) ≫
        @Scheme.ConormalAlgebra.symmetricToTotal _ _ (rankHom q p i hi V r).left
          (rankHom_isImmersion q p i hi V r) := sorry

/-- The associated vector-bundle total space over a virtual-normal rank locus. -/
noncomputable def normalOver {S Z X : Scheme.{u}} (q : Z ⟶ S) (i : Z ⟶ X)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ)
    (P : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra (Scheme.Modules.dual (rankModule i V r))))
    [Scheme.IsRelativeSpectrumOver P] : Over S :=
  Over.mk (Scheme.associatedVectorBundleπ (Scheme.Modules.dual (rankModule i V r)) P ≫
    (BivariantClass.OpenRestriction.over (Over.mk q) (@rankOpen Z X i h_i V r)).hom)

/-- A chosen associated-vector-bundle total space is locally of finite type over `S`. -/
theorem normalOver_locallyOfFiniteType {S Z X : Scheme.{u}} (q : Z ⟶ S)
    [LocallyOfFiniteType q] (i : Z ⟶ X) [h_i : IsImmersion i]
    (V : VirtualNormalBundle i) (r : ℕ)
    (P : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra (Scheme.Modules.dual (rankModule i V r))))
    (hP : Scheme.IsRelativeSpectrumOver P) :
    LocallyOfFiniteType (@normalOver S Z X q i h_i V r P hP).hom := sorry

/-- The associated vector-bundle projection over `S` on a rank locus. -/
noncomputable def normalProjection {S Z X : Scheme.{u}} (q : Z ⟶ S) (i : Z ⟶ X)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ)
    (P : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra (Scheme.Modules.dual (rankModule i V r))))
    [Scheme.IsRelativeSpectrumOver P] :
    normalOver q i V r P ⟶
      BivariantClass.OpenRestriction.over (Over.mk q) (@rankOpen Z X i h_i V r) :=
  Over.homMk (Scheme.associatedVectorBundleπ (Scheme.Modules.dual (rankModule i V r)) P)

/-- The underlying map of `normalProjection` is the associated vector-bundle projection. -/
theorem normalProjection_left {S Z X : Scheme.{u}} (q : Z ⟶ S) (i : Z ⟶ X)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ)
    (P : Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra (Scheme.Modules.dual (rankModule i V r))))
    [Scheme.IsRelativeSpectrumOver P] :
    (normalProjection q i V r P).left =
      Scheme.associatedVectorBundleπ (Scheme.Modules.dual (rankModule i V r)) P := sorry

/-- The part of the actual normal cone lying over the rank-`r` locus. -/
noncomputable def rankNormalCone {Z X : Scheme.{u}} (i : Z ⟶ X) [h_i : IsImmersion i]
    (V : VirtualNormalBundle i) (r : ℕ)
    (P : Scheme.RelativeSpectrumOver (Scheme.ConormalAlgebra.total i))
    [Scheme.IsRelativeSpectrumOver P] : Scheme.{u} :=
  Limits.pullback (Scheme.normalConeπ i P)
    (Scheme.Opens.ι (@rankOpen Z X i h_i V r))

/-- The rankwise normal cone is the canonical pullback of `C(Z/X)` to the corresponding
rank locus. -/
theorem rankNormalCone_def {Z X : Scheme.{u}} (i : Z ⟶ X) [h_i : IsImmersion i]
    (V : VirtualNormalBundle i) (r : ℕ)
    (P : Scheme.RelativeSpectrumOver (Scheme.ConormalAlgebra.total i))
    [Scheme.IsRelativeSpectrumOver P] :
    rankNormalCone i V r P = Limits.pullback (Scheme.normalConeπ i P)
      (Scheme.Opens.ι (@rankOpen Z X i h_i V r)) := sorry

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

/-- The rankwise normal-cone embedding is the pullback projection followed by the global
normal-cone embedding. -/
theorem rankNormalConeEmbedding_def
    {S Z X W : Scheme.{u}} (p : X ⟶ S) (i : Z ⟶ X) [h_i : IsImmersion i]
    (V : VirtualNormalBundle i) (r : ℕ)
    (P : Scheme.RelativeSpectrumOver (Scheme.ConormalAlgebra.total i))
    [Scheme.IsRelativeSpectrumOver P]
    (b : W ⟶ ProjectiveLineFamily.space (Over.mk p))
    (e : Scheme.normalCone i P ⟶
      (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) b).left) :
    rankNormalConeEmbedding p i V r P b e =
      pullback.fst (Scheme.normalConeπ i P)
        (Scheme.Opens.ι (@rankOpen Z X i h_i V r)) ≫ e := sorry

end ClosedSpecialization

/-- Explicit source construction data for the deformation to the normal cone of a closed
immersion and a virtual normal bundle. A value records chosen representatives of the blowup
and of the actual normal cone used in the source construction; it is not an arbitrary
compactification. The proof fields record the geometric validity of those representatives. -/
structure ClosedSpecialization
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (V : VirtualNormalBundle i) : Type (u + 1) where
  /-- The chosen blowup deformation space from the source construction. -/
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
    (Scheme.SymmetricAlgebra.qcAlgebra
      (Scheme.Modules.dual (ClosedSpecialization.rankModule i V r)))
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
    (@ClosedSpecialization.rankNormalConeEmbedding S Z X deformationSpace p i
      (IsImmersion.instOfIsClosedImmersion i) V r normalConeModel normalConeModelSpec
      deformationMap normalConeEmbedding)
  /-- The actual normal cone from the source construction, represented as an open of the
  fibre at infinity rank locus by rank locus. -/
  coneOpen : (r : ℕ) →
    (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) deformationMap).left.Opens
  /-- The rank-`r` cone open is exactly the image of the actual normal cone over the rank
  locus of the virtual normal bundle. -/
  coneOpen_eq : (r : ℕ) → coneOpen r =
    @Scheme.Hom.opensRange _ _
      (@ClosedSpecialization.rankNormalConeEmbedding S Z X deformationSpace p i
        (IsImmersion.instOfIsClosedImmersion i) V r normalConeModel normalConeModelSpec
        deformationMap normalConeEmbedding) (rankNormalConeEmbeddingOpen r)
  /-- Each normal-cone open maps into the top open of `X`. -/
  coneOpen_le : (r : ℕ) → coneOpen r ≤
    (BivariantClass.GysinAtInfinity.infinityToX (Over.mk p) deformationMap).left ⁻¹ᵁ
      (⊤ : X.Opens)
  /-- A relative-spectrum model of the actual normal cone after restriction to the rank
  locus. -/
  rankNormalConeModel : (r : ℕ) → Scheme.RelativeSpectrumOver
    (@Scheme.ConormalAlgebra.total _ _ (ClosedSpecialization.rankHom q p i hi V r).left
      (ClosedSpecialization.rankHom_isImmersion q p i hi V r))
  /-- Each rankwise normal-cone model represents the total conormal algebra. -/
  rankNormalConeModelSpec : (r : ℕ) →
    Scheme.IsRelativeSpectrumOver (rankNormalConeModel r)
  /-- The cone open in the deformation fibre is identified with the corresponding
  rankwise normal cone. -/
  rankNormalConeIso : (r : ℕ) →
    (BivariantClass.OpenRestriction.over
      (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) deformationMap)
      (coneOpen r)).left ≅
        @Scheme.normalCone _ _ (ClosedSpecialization.rankHom q p i hi V r).left
          (ClosedSpecialization.rankHom_isImmersion q p i hi V r)
          (rankNormalConeModel r) (rankNormalConeModelSpec r)
  /-- The closed map from the normal cone to the chosen normal-bundle model. -/
  coneToNormal : (r : ℕ) →
    BivariantClass.OpenRestriction.over
        (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) deformationMap)
        (coneOpen r) ⟶
      ClosedSpecialization.normalOver q i V r (normalModel r)
  /-- The cone-to-normal map is exactly the relative-spectrum morphism induced by the
  restricted quotient `V.map`, followed by the symmetric-to-total conormal algebra map. -/
  coneToNormal_eq_relativeSpecMap : (r : ℕ) → (coneToNormal r).left =
    (rankNormalConeIso r).hom ≫
      @Scheme.relativeSpecMap _ _ _
        (ClosedSpecialization.rankNormalAlgebraMap q p i hi V r)
        (normalModel r) (normalModelSpec r)
        (rankNormalConeModel r) (rankNormalConeModelSpec r)
  /-- The comparison from the normal cone to the normal bundle is a closed immersion. -/
  coneToNormalClosed : (r : ℕ) → IsClosedImmersion (coneToNormal r).left
  /-- The cone-to-normal comparison respects the maps to `X`. -/
  coneToNormal_over : (r : ℕ) →
    coneToNormal r ≫
        (ClosedSpecialization.normalProjection q i V r (normalModel r) ≫
          ClosedSpecialization.rankHom q p i hi V r) =
      BivariantClass.OpenRestriction.hom
        (BivariantClass.GysinAtInfinity.infinityToX (Over.mk p) deformationMap)
        (coneOpen r) ⊤ (coneOpen_le r)

namespace ClosedSpecialization

/-- Construct explicit specialization input from its deformation, normal-bundle, and
normal-cone comparison data. -/
def ofGysinAtInfinity
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (V : VirtualNormalBundle i) (W : Scheme.{u})
    (b : W ⟶ ProjectiveLineFamily.space (Over.mk p))
    (hblowup : IsBlowup b
      (i ≫ ProjectiveLineFamily.infinitySection (Over.mk p)).ker)
    (hproper : IsProper b)
    (haffine : IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart (Over.mk p)))
    (P : (r : ℕ) → Scheme.RelativeSpectrumOver
      (Scheme.SymmetricAlgebra.qcAlgebra (Scheme.Modules.dual (rankModule i V r))))
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
      (BivariantClass.OpenRestriction.over
        (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) b) (U r)).left ≅
          @Scheme.normalCone _ _ (rankHom q p i hi V r).left
            (rankHom_isImmersion q p i hi V r) (PRC r) (hPRC r))
    (k : (r : ℕ) → BivariantClass.OpenRestriction.over
        (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) b) (U r) ⟶
      normalOver q i V r (P r))
    (hk_eq : (r : ℕ) → (k r).left = (eRC r).hom ≫
      @Scheme.relativeSpecMap _ _ _
        (rankNormalAlgebraMap q p i hi V r)
        (P r) (hP r) (PRC r) (hPRC r))
    (hk_closed : (r : ℕ) → IsClosedImmersion (k r).left)
    (hk_over : (r : ℕ) → k r ≫
        (normalProjection q i V r (P r) ≫ rankHom q p i hi V r) =
      BivariantClass.OpenRestriction.hom
        (BivariantClass.GysinAtInfinity.infinityToX (Over.mk p) b) (U r) ⊤ (hU r)) :
    ClosedSpecialization delta q p i hi V where
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
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V) :
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
            (D.rankNormalConeModel r) (D.rankNormalConeModelSpec r) := sorry

/-- The homogeneous bivariant-class group on one virtual-normal rank locus. -/
abbrev RankClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (r : ℕ) (n : ℤ) : Type (u + 1) :=
  BivariantClass delta (rankHom q p i hi V r) n

/-- `RankClass` is the ordinary bivariant-class group of the restricted morphism. -/
theorem rankClass_def
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (r : ℕ) (n : ℤ) :
    RankClass delta q p i hi V r n = BivariantClass delta (rankHom q p i hi V r) n := sorry

/-- The degree-zero bivariant-class group on a chosen normal-bundle total space. -/
abbrev AmbientClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V) (r : ℕ) :
    Type (u + 1) :=
  @BivariantClass S _ delta _ _ _
    (normalOver_locallyOfFiniteType q i V r (D.normalModel r) (D.normalModelSpec r)) _
    (@normalProjection S Z X q i _ V r (D.normalModel r) (D.normalModelSpec r) ≫
      rankHom q p i hi V r) 0

/-- `AmbientClass` is the degree-zero group for the normal projection followed by the
rank-locus immersion. -/
theorem ambientClassType_def
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V) (r : ℕ) :
    AmbientClass delta q p i hi V D r =
      @BivariantClass S _ delta _ _ _
        (normalOver_locallyOfFiniteType q i V r (D.normalModel r) (D.normalModelSpec r)) _
        (@normalProjection S Z X q i _ V r (D.normalModel r) (D.normalModelSpec r) ≫
          rankHom q p i hi V r) 0 := sorry

/-- The canonical Gysin-at-infinity class attached to a specialization model. -/
noncomputable def gysinClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V) :
    BivariantClass delta
      (BivariantClass.GysinAtInfinity.infinityToX (Over.mk p) D.deformationMap) 0 :=
  @BivariantClass.gysinAtInfinity S D.deformationSpace _ delta _ (Over.mk p) _
    D.deformationMap D.deformationProper D.deformationAffineIso

/-- The Gysin class uses the deformation morphism stored in the specialization model. -/
theorem gysinClass_def
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V) :
    gysinClass delta q p i hi V D =
      @BivariantClass.gysinAtInfinity S D.deformationSpace _ delta _ (Over.mk p) _
        D.deformationMap D.deformationProper D.deformationAffineIso := sorry

/-- The closed cone-to-normal comparison is proper. -/
theorem coneToNormal_proper
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V) (r : ℕ) :
    IsProper (D.coneToNormal r).left := sorry

/-- The degree-zero class on the normal-bundle total space obtained by restricting the
Gysin-at-infinity class to the cone and pushing it forward. -/
noncomputable def ambientClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V) (r : ℕ) :
    AmbientClass delta q p i hi V D r :=
  @BivariantClass.pushforward S _ delta _ _ _ _ _
    (normalOver_locallyOfFiniteType q i V r (D.normalModel r) (D.normalModelSpec r)) _
    (D.coneToNormal r) (coneToNormal_proper delta q p i hi V D r)
    (@normalProjection S Z X q i _ V r (D.normalModel r) (D.normalModelSpec r) ≫
      rankHom q p i hi V r) 0
    ((D.coneToNormal_over r).symm ▸
      BivariantClass.OpenRestriction.restrict delta
        (BivariantClass.GysinAtInfinity.infinityToX (Over.mk p) D.deformationMap) 0
        (D.coneOpen r) ⊤ (D.coneOpen_le r) (gysinClass delta q p i hi V D))

/-- The ambient class is the proper pushforward of the cone restriction of the
Gysin-at-infinity class. -/
theorem ambientClass_spec
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V) (r : ℕ) :
    ambientClass delta q p i hi V D r =
      @BivariantClass.pushforward S _ delta _ _ _ _ _
        (normalOver_locallyOfFiniteType q i V r (D.normalModel r) (D.normalModelSpec r)) _
        (D.coneToNormal r) (coneToNormal_proper delta q p i hi V D r)
        (@normalProjection S Z X q i _ V r (D.normalModel r) (D.normalModelSpec r) ≫
          rankHom q p i hi V r) 0
        ((D.coneToNormal_over r).symm ▸
          BivariantClass.OpenRestriction.restrict delta
            (BivariantClass.GysinAtInfinity.infinityToX (Over.mk p) D.deformationMap) 0
            (D.coneOpen r) ⊤ (D.coneOpen_le r) (gysinClass delta q p i hi V D)) := sorry

end ClosedSpecialization

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

namespace AlgebraicGeometry.BivariantClass

/-- The grading identity for composing a degree-`-r` vector-bundle pullback class with a
degree-`r` bivariant class. -/
theorem vectorBundleCompositionDegree (r : ℕ) : -(r : ℤ) + (r : ℤ) = 0 := sorry

/-- The associated vector-bundle projection over an `Over` object is flat. -/
noncomputable instance vectorBundleProjection_flat
    {S : Scheme.{u}} (X : Over S) (E : X.left.Modules)
    [Scheme.Modules.IsFiniteLocallyFree E]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra E))
    [Scheme.IsRelativeSpectrumOver P] :
    Flat
      (Over.Hom.left (Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X)) :=
  Scheme.AssociatedVectorBundle.overHomFlat X E P

/-- The same associated projection has the expected relative dimension. -/
noncomputable instance vectorBundleProjection_relativeDimension
    {S : Scheme.{u}} (X : Over S) (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra E))
    [Scheme.IsRelativeSpectrumOver P] :
    Scheme.Hom.RelativeDimension
      (Over.Hom.left (Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X)) r :=
  Scheme.AssociatedVectorBundle.overHomRelativeDimension X E r P

/-- Composition with flat pullback along a rank-`r` associated vector bundle. -/
noncomputable def vectorBundleComposition
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra E))
    [Scheme.IsRelativeSpectrumOver P] :
    BivariantClass delta f (r : ℤ) →+
    BivariantClass delta
        ((Over.homMk (Scheme.associatedVectorBundleπ E P) :
          Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) ≫ f) 0 where
  toFun c := vectorBundleCompositionDegree r ▸
    comp delta
      (Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X)
      f (flatPullback delta
        (Over.homMk (Scheme.associatedVectorBundleπ E P) :
          Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) r) c
  map_zero' := sorry
  map_add' := sorry

/-- Vector-bundle composition is bijective on bivariant classes. -/
theorem vectorBundleComposition_bijective
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra E))
    [Scheme.IsRelativeSpectrumOver P] :
    Function.Bijective (vectorBundleComposition delta f E r P) := sorry

/-- Degree-`r` classes are additively equivalent to degree-zero classes after composition
with rank-`r` vector-bundle flat pullback. -/
noncomputable def vectorBundleCompositionEquiv
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra E))
    [Scheme.IsRelativeSpectrumOver P] :
    BivariantClass delta f (r : ℤ) ≃+
      BivariantClass delta
        ((Over.homMk (Scheme.associatedVectorBundleπ E P) :
          Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) ≫ f) 0 where
  toFun := vectorBundleComposition delta f E r P
  invFun := Function.invFun (vectorBundleComposition delta f E r P)
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- The forward map of `vectorBundleCompositionEquiv` is composition with vector-bundle
flat pullback. -/
theorem vectorBundleCompositionEquiv_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra E))
    [Scheme.IsRelativeSpectrumOver P] (c : BivariantClass delta f (r : ℤ)) :
    vectorBundleCompositionEquiv delta f E r P c =
      vectorBundleComposition delta f E r P c := sorry

/-- Applying vector-bundle composition to its chosen inverse recovers the degree-zero
class. -/
theorem vectorBundleCompositionEquiv_symm_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (E : X.left.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra E))
    [Scheme.IsRelativeSpectrumOver P]
    (c : BivariantClass delta
      ((Over.homMk (Scheme.associatedVectorBundleπ E P) :
        Over.mk (Scheme.associatedVectorBundleπ E P ≫ X.hom) ⟶ X) ≫ f) 0) :
    vectorBundleComposition delta f E r P
      ((vectorBundleCompositionEquiv delta f E r P).symm c) = c := sorry

end AlgebraicGeometry.BivariantClass

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

/-- The homogeneous degree-`r` class obtained by descending the degree-zero specialization
class through vector-bundle flat pullback. -/
noncomputable def closedClassOfRank
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V) (r : ℕ) :
    BivariantClass delta (ClosedSpecialization.rankHom q p i hi V r) (r : ℤ) :=
  Function.invFun (@BivariantClass.vectorBundleComposition S _ delta _ _ _ _ _
    (ClosedSpecialization.rankHom q p i hi V r)
    (Scheme.Modules.dual (ClosedSpecialization.rankModule i V r)) r
    (ClosedSpecialization.rankDualModule_isFiniteLocallyFreeOfRank i V r)
    (D.normalModel r) (D.normalModelSpec r))
    (ClosedSpecialization.ambientClass delta q p i hi V D r)

/-- Pulling `closedClassOfRank` back to the normal-bundle total space recovers the
degree-zero specialization class. -/
theorem closedClassOfRank_spec
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V) (r : ℕ) :
    @BivariantClass.vectorBundleComposition S _ delta _ _ _ _ _
      (ClosedSpecialization.rankHom q p i hi V r)
      (Scheme.Modules.dual (ClosedSpecialization.rankModule i V r)) r
      (ClosedSpecialization.rankDualModule_isFiniteLocallyFreeOfRank i V r)
      (D.normalModel r) (D.normalModelSpec r)
      (closedClassOfRank delta q p i hi V D r) =
        ClosedSpecialization.ambientClass delta q p i hi V D r := sorry

/-- The completed virtual-normal class, with the degree-`r` class placed on the rank-`r`
clopen locus. -/
noncomputable def closedClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V) :
    BivariantClass.OpenRestriction.Completion delta (overHom q p i hi)
      (fun r : ℕ ↦ @rankOpen Z X i
        (inferInstance : IsImmersion i) V r)
      (fun _ : Unit ↦ ⊤) (fun _ ↦ Unit.unit)
      (fun r ↦ rankOpen_le_preimage_top q p i hi V r) :=
  fun r ↦ DirectSum.of
    (fun n : ℕ ↦ BivariantClass delta
      (ClosedSpecialization.rankHom q p i hi V r) (n : ℤ)) r
    (closedClassOfRank delta q p i hi V D r)

/-- The degree matching a rank locus is its descended homogeneous class. -/
theorem closedClass_component
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V) (r : ℕ) :
    closedClass delta q p i hi V D r r = closedClassOfRank delta q p i hi V D r := sorry

/-- Every degree other than the rank vanishes on a fixed rank locus. -/
theorem closedClass_component_ne
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V)
    (r n : ℕ) (hne : n ≠ r) : closedClass delta q p i hi V D r n = 0 := sorry

namespace ClosedSpecialization

/-- The rankwise vector-bundle composition map used to descend the specialization class. -/
noncomputable def composition
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V) (r : ℕ) :
    RankClass delta q p i hi V r (r : ℤ) →+ AmbientClass delta q p i hi V D r :=
  @BivariantClass.vectorBundleComposition S _ delta _ _ _ _ _
    (rankHom q p i hi V r) (Scheme.Modules.dual (rankModule i V r)) r
    (rankDualModule_isFiniteLocallyFreeOfRank i V r)
    (D.normalModel r) (D.normalModelSpec r)

/-- Evaluation of `composition` is the canonical vector-bundle composition map. -/
theorem composition_apply
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V) (r : ℕ)
    (c : RankClass delta q p i hi V r (r : ℤ)) :
    composition delta q p i hi V D r c =
      @BivariantClass.vectorBundleComposition S _ delta _ _ _ _ _
        (rankHom q p i hi V r) (Scheme.Modules.dual (rankModule i V r)) r
        (rankDualModule_isFiniteLocallyFreeOfRank i V r)
        (D.normalModel r)
        (D.normalModelSpec r) c := sorry

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
    BivariantClass.OpenRestriction.over (Over.mk q')
        (@rankOpen Z' X' i' (IsImmersion.instOfIsClosedImmersion i')
          (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
            (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
            square V) r) ⟶
      BivariantClass.OpenRestriction.over (Over.mk q)
        (@rankOpen Z X i (IsImmersion.instOfIsClosedImmersion i) V r) :=
  BivariantClass.OpenRestriction.hom g
    (@rankOpen Z' X' i' (IsImmersion.instOfIsClosedImmersion i')
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) r)
    (@rankOpen Z X i (IsImmersion.instOfIsClosedImmersion i) V r)
    (rankOpen_le_baseChange_preimage q p q' p' i hi i' hi' g f square V r)

/-- The top open of the base-changed target maps into the original top open. -/
theorem top_le_baseChange_preimage
    {S X X' : Scheme.{u}} (p : X ⟶ S) (p' : X' ⟶ S)
    (f : Over.mk p' ⟶ Over.mk p) :
    (⊤ : X'.Opens) ≤ f.left ⁻¹ᵁ (⊤ : X.Opens) := sorry

/-- The canonical map between the top-open restrictions of the two targets. -/
noncomputable def topBaseChangeTarget
    {S X X' : Scheme.{u}} (p : X ⟶ S) (p' : X' ⟶ S)
    (f : Over.mk p' ⟶ Over.mk p) :
    BivariantClass.OpenRestriction.over (Over.mk p') ⊤ ⟶
      BivariantClass.OpenRestriction.over (Over.mk p) ⊤ :=
  BivariantClass.OpenRestriction.hom f ⊤ ⊤ (top_le_baseChange_preimage p p' f)

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

/-- The geometric comparison between the deformation-to-the-normal-cone data before and
after a cartesian base change.  The closed-immersion fields are the three comparison maps
into the fibre products displayed in the source proof. -/
structure BaseChange
    {S Z X Z' X' : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    (q' : Z' ⟶ S) (p' : X' ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    [LocallyOfFiniteType q'] [LocallyOfFiniteType p']
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (i' : Z' ⟶ X') (hi' : i' ≫ p' = q') [h_i' : IsClosedImmersion i']
    (g : Over.mk q' ⟶ Over.mk q) (f : Over.mk p' ⟶ Over.mk p)
    (square : IsPullback g.left i' i f.left) (V : VirtualNormalBundle i)
    (D : ClosedSpecialization delta q p i hi V)
    (D' : ClosedSpecialization delta q' p' i' hi'
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V)) : Type (u + 1) where
  /-- The comparison from the base-changed deformation space to the original one. -/
  deformationComparison :
    BivariantClass.GysinAtInfinity.compactification (Over.mk p') D'.deformationMap ⟶
      BivariantClass.GysinAtInfinity.compactification (Over.mk p) D.deformationMap
  /-- The induced map from the new deformation space into the fibre product of the old
  deformation space with `ProjectiveLineFamily.space (Over.mk p')`. -/
  deformationIntoPullback : D'.deformationSpace ⟶
    Limits.pullback D.deformationMap (ProjectiveLineFamily.map f)
  /-- The first projection of the deformation comparison is the map to the old deformation. -/
  deformation_fst : deformationIntoPullback ≫
    pullback.fst D.deformationMap (ProjectiveLineFamily.map f) = deformationComparison.left
  /-- The second projection of the deformation comparison is the new deformation map. -/
  deformation_snd : deformationIntoPullback ≫
    pullback.snd D.deformationMap (ProjectiveLineFamily.map f) = D'.deformationMap
  /-- The comparison with the base-changed deformation space is a closed immersion. -/
  deformationClosed : IsClosedImmersion deformationIntoPullback
  /-- The comparison between the two fibres at infinity. -/
  infinityComparison :
    BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p') D'.deformationMap ⟶
      BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) D.deformationMap
  /-- The infinity-fibre comparison commutes with the inclusions into the deformation spaces. -/
  infinity_deformation : infinityComparison ≫
      BivariantClass.GysinAtInfinity.infinityInclusion (Over.mk p) D.deformationMap =
    BivariantClass.GysinAtInfinity.infinityInclusion (Over.mk p') D'.deformationMap ≫
      deformationComparison
  /-- The induced map from the new infinity fibre into the base change of the old one. -/
  infinityIntoPullback :
    (BivariantClass.GysinAtInfinity.infinityFiber
      (Over.mk p') D'.deformationMap).left ⟶
      Limits.pullback
        (BivariantClass.GysinAtInfinity.infinityToX
          (Over.mk p) D.deformationMap).left f.left
  /-- The first projection of the infinity-fibre comparison is the map to the old fibre. -/
  infinity_fst : infinityIntoPullback ≫
      pullback.fst
        (BivariantClass.GysinAtInfinity.infinityToX
          (Over.mk p) D.deformationMap).left f.left = infinityComparison.left
  /-- The second projection of the infinity-fibre comparison is its map to `X'`. -/
  infinity_snd : infinityIntoPullback ≫
      pullback.snd
        (BivariantClass.GysinAtInfinity.infinityToX
          (Over.mk p) D.deformationMap).left f.left =
    (BivariantClass.GysinAtInfinity.infinityToX
      (Over.mk p') D'.deformationMap).left
  /-- The comparison with the base-changed infinity fibre is a closed immersion. -/
  infinityClosed : IsClosedImmersion infinityIntoPullback
  /-- The canonical comparison from the pulled actual normal cone to the original actual
  normal cone. -/
  normalConeComparison :
    @Scheme.normalCone X' Z' i' (IsImmersion.instOfIsClosedImmersion i')
        D'.normalConeModel D'.normalConeModelSpec ⟶
      @Scheme.normalCone X Z i (IsImmersion.instOfIsClosedImmersion i)
        D.normalConeModel D.normalConeModelSpec
  /-- The map from the pulled normal cone into the base change of the original normal cone. -/
  normalConeIntoPullback :
    @Scheme.normalCone X' Z' i' (IsImmersion.instOfIsClosedImmersion i')
        D'.normalConeModel D'.normalConeModelSpec ⟶
      Limits.pullback
        (@Scheme.normalConeπ X Z i (IsImmersion.instOfIsClosedImmersion i)
          D.normalConeModel D.normalConeModelSpec) g.left
  /-- The first projection of the actual-normal-cone comparison is its canonical map to the
  original normal cone. -/
  normalCone_fst : normalConeIntoPullback ≫
      pullback.fst
        (@Scheme.normalConeπ X Z i (IsImmersion.instOfIsClosedImmersion i)
          D.normalConeModel D.normalConeModelSpec) g.left = normalConeComparison
  /-- The second projection of the actual-normal-cone comparison is the structural map of the
  pulled normal cone. -/
  normalCone_snd : normalConeIntoPullback ≫
      pullback.snd
        (@Scheme.normalConeπ X Z i (IsImmersion.instOfIsClosedImmersion i)
          D.normalConeModel D.normalConeModelSpec) g.left =
    @Scheme.normalConeπ X' Z' i' (IsImmersion.instOfIsClosedImmersion i')
      D'.normalConeModel D'.normalConeModelSpec
  /-- The canonical comparison with the base change of the actual normal cone is a closed
  immersion. -/
  normalConeClosed : IsClosedImmersion normalConeIntoPullback
  /-- The actual-normal-cone comparison agrees with the comparison of the fibres at infinity. -/
  normalCone_infinity : normalConeComparison ≫ D.normalConeEmbedding =
    D'.normalConeEmbedding ≫ infinityComparison.left
  /-- The comparison between the actual normal-cone opens in the two infinity fibres. -/
  coneComparison : (r : ℕ) →
    BivariantClass.OpenRestriction.over
        (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p') D'.deformationMap)
        (D'.coneOpen r) ⟶
      BivariantClass.OpenRestriction.over
        (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) D.deformationMap)
        (D.coneOpen r)
  /-- The normal-cone comparison commutes with the inclusions into the infinity fibres. -/
  cone_infinity : (r : ℕ) → coneComparison r ≫
      BivariantClass.OpenRestriction.ι
        (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) D.deformationMap)
        (D.coneOpen r) =
    BivariantClass.OpenRestriction.ι
        (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p') D'.deformationMap)
        (D'.coneOpen r) ≫ infinityComparison
  /-- The map from the new normal cone into the base change of the old normal cone. -/
  coneIntoPullback : (r : ℕ) →
    (BivariantClass.OpenRestriction.over
      (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p') D'.deformationMap)
      (D'.coneOpen r)).left ⟶
      Limits.pullback
        ((D.coneToNormal r ≫ @normalProjection S Z X q i _ V r
          (D.normalModel r) (D.normalModelSpec r)).left)
        (rankBaseChangeSource q p q' p' i hi i' hi' g f square V r).left
  /-- The first projection of the normal-cone comparison is its map to the old cone. -/
  cone_fst : (r : ℕ) → coneIntoPullback r ≫
      pullback.fst
        ((D.coneToNormal r ≫ @normalProjection S Z X q i _ V r
          (D.normalModel r) (D.normalModelSpec r)).left)
        (rankBaseChangeSource q p q' p' i hi i' hi' g f square V r).left =
    (coneComparison r).left
  /-- The second projection of the normal-cone comparison is its map to the new rank locus. -/
  cone_snd : (r : ℕ) → coneIntoPullback r ≫
      pullback.snd
        ((D.coneToNormal r ≫ @normalProjection S Z X q i _ V r
          (D.normalModel r) (D.normalModelSpec r)).left)
        (rankBaseChangeSource q p q' p' i hi i' hi' g f square V r).left =
    (D'.coneToNormal r ≫ @normalProjection S Z' X' q' i' _
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) r (D'.normalModel r) (D'.normalModelSpec r)).left
  /-- The comparison with the base-changed normal cone is a closed immersion. -/
  coneClosed : (r : ℕ) → IsClosedImmersion (coneIntoPullback r)
  /-- The comparison between the chosen models of the two normal bundles. -/
  normalComparison : (r : ℕ) →
    @normalOver S Z' X' q' i' _
        (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
          (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
          square V) r (D'.normalModel r) (D'.normalModelSpec r) ⟶
      @normalOver S Z X q i _ V r (D.normalModel r) (D.normalModelSpec r)
  /-- The normal-bundle comparison is the cartesian base change along the rank loci. -/
  normalSquare : (r : ℕ) → IsPullback (normalComparison r).left
    (@normalProjection S Z' X' q' i' _
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) r (D'.normalModel r) (D'.normalModelSpec r)).left
    (@normalProjection S Z X q i _ V r
      (D.normalModel r) (D.normalModelSpec r)).left
    (rankBaseChangeSource q p q' p' i hi i' hi' g f square V r).left
  /-- The normal comparison respects the quotient-induced cone maps for the original and
  pulled virtual normal bundles. -/
  cone_normal : (r : ℕ) → coneComparison r ≫ D.coneToNormal r =
    D'.coneToNormal r ≫ normalComparison r

namespace BaseChange

/-- Construct a geometric base-change comparison from the three closed comparison maps and
the cartesian normal-bundle square occurring in the deformation argument. -/
def ofComparison
    {S Z X Z' X' : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    (q' : Z' ⟶ S) (p' : X' ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    [LocallyOfFiniteType q'] [LocallyOfFiniteType p']
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (i' : Z' ⟶ X') (hi' : i' ≫ p' = q') [h_i' : IsClosedImmersion i']
    (g : Over.mk q' ⟶ Over.mk q) (f : Over.mk p' ⟶ Over.mk p)
    (square : IsPullback g.left i' i f.left) (V : VirtualNormalBundle i)
    (D : ClosedSpecialization delta q p i hi V)
    (D' : ClosedSpecialization delta q' p' i' hi'
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V))
    (deformationComparison :
      BivariantClass.GysinAtInfinity.compactification (Over.mk p') D'.deformationMap ⟶
        BivariantClass.GysinAtInfinity.compactification (Over.mk p) D.deformationMap)
    (deformationIntoPullback : D'.deformationSpace ⟶
      Limits.pullback D.deformationMap (ProjectiveLineFamily.map f))
    (deformation_fst : deformationIntoPullback ≫
      pullback.fst D.deformationMap (ProjectiveLineFamily.map f) = deformationComparison.left)
    (deformation_snd : deformationIntoPullback ≫
      pullback.snd D.deformationMap (ProjectiveLineFamily.map f) = D'.deformationMap)
    (deformationClosed : IsClosedImmersion deformationIntoPullback)
    (infinityComparison :
      BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p') D'.deformationMap ⟶
        BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) D.deformationMap)
    (infinity_deformation : infinityComparison ≫
        BivariantClass.GysinAtInfinity.infinityInclusion (Over.mk p) D.deformationMap =
      BivariantClass.GysinAtInfinity.infinityInclusion (Over.mk p') D'.deformationMap ≫
        deformationComparison)
    (infinityIntoPullback :
      (BivariantClass.GysinAtInfinity.infinityFiber
        (Over.mk p') D'.deformationMap).left ⟶
        Limits.pullback
          (BivariantClass.GysinAtInfinity.infinityToX
            (Over.mk p) D.deformationMap).left f.left)
    (infinity_fst : infinityIntoPullback ≫
        pullback.fst
          (BivariantClass.GysinAtInfinity.infinityToX
            (Over.mk p) D.deformationMap).left f.left = infinityComparison.left)
    (infinity_snd : infinityIntoPullback ≫
        pullback.snd
          (BivariantClass.GysinAtInfinity.infinityToX
            (Over.mk p) D.deformationMap).left f.left =
      (BivariantClass.GysinAtInfinity.infinityToX
        (Over.mk p') D'.deformationMap).left)
    (infinityClosed : IsClosedImmersion infinityIntoPullback)
    (normalConeComparison :
      @Scheme.normalCone X' Z' i' (IsImmersion.instOfIsClosedImmersion i')
          D'.normalConeModel D'.normalConeModelSpec ⟶
        @Scheme.normalCone X Z i (IsImmersion.instOfIsClosedImmersion i)
          D.normalConeModel D.normalConeModelSpec)
    (normalConeIntoPullback :
      @Scheme.normalCone X' Z' i' (IsImmersion.instOfIsClosedImmersion i')
          D'.normalConeModel D'.normalConeModelSpec ⟶
        Limits.pullback
          (@Scheme.normalConeπ X Z i (IsImmersion.instOfIsClosedImmersion i)
            D.normalConeModel D.normalConeModelSpec) g.left)
    (normalCone_fst : normalConeIntoPullback ≫
        pullback.fst
          (@Scheme.normalConeπ X Z i (IsImmersion.instOfIsClosedImmersion i)
            D.normalConeModel D.normalConeModelSpec) g.left = normalConeComparison)
    (normalCone_snd : normalConeIntoPullback ≫
        pullback.snd
          (@Scheme.normalConeπ X Z i (IsImmersion.instOfIsClosedImmersion i)
            D.normalConeModel D.normalConeModelSpec) g.left =
      @Scheme.normalConeπ X' Z' i' (IsImmersion.instOfIsClosedImmersion i')
        D'.normalConeModel D'.normalConeModelSpec)
    (normalConeClosed : IsClosedImmersion normalConeIntoPullback)
    (normalCone_infinity : normalConeComparison ≫ D.normalConeEmbedding =
      D'.normalConeEmbedding ≫ infinityComparison.left)
    (coneComparison : (r : ℕ) →
      BivariantClass.OpenRestriction.over
          (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p') D'.deformationMap)
          (D'.coneOpen r) ⟶
        BivariantClass.OpenRestriction.over
          (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) D.deformationMap)
          (D.coneOpen r))
    (cone_infinity : (r : ℕ) → coneComparison r ≫
        BivariantClass.OpenRestriction.ι
          (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p) D.deformationMap)
          (D.coneOpen r) =
      BivariantClass.OpenRestriction.ι
          (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p') D'.deformationMap)
          (D'.coneOpen r) ≫ infinityComparison)
    (coneIntoPullback : (r : ℕ) →
      (BivariantClass.OpenRestriction.over
        (BivariantClass.GysinAtInfinity.infinityFiber (Over.mk p') D'.deformationMap)
        (D'.coneOpen r)).left ⟶
        Limits.pullback
          ((D.coneToNormal r ≫ @normalProjection S Z X q i _ V r
            (D.normalModel r) (D.normalModelSpec r)).left)
          (rankBaseChangeSource q p q' p' i hi i' hi' g f square V r).left)
    (cone_fst : (r : ℕ) → coneIntoPullback r ≫
        pullback.fst
          ((D.coneToNormal r ≫ @normalProjection S Z X q i _ V r
            (D.normalModel r) (D.normalModelSpec r)).left)
          (rankBaseChangeSource q p q' p' i hi i' hi' g f square V r).left =
      (coneComparison r).left)
    (cone_snd : (r : ℕ) → coneIntoPullback r ≫
        pullback.snd
          ((D.coneToNormal r ≫ @normalProjection S Z X q i _ V r
            (D.normalModel r) (D.normalModelSpec r)).left)
          (rankBaseChangeSource q p q' p' i hi i' hi' g f square V r).left =
      (D'.coneToNormal r ≫ @normalProjection S Z' X' q' i' _
        (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
          (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
          square V) r (D'.normalModel r) (D'.normalModelSpec r)).left)
    (coneClosed : (r : ℕ) → IsClosedImmersion (coneIntoPullback r))
    (normalComparison : (r : ℕ) →
      @normalOver S Z' X' q' i' _
          (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
            (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
            square V) r (D'.normalModel r) (D'.normalModelSpec r) ⟶
        @normalOver S Z X q i _ V r (D.normalModel r) (D.normalModelSpec r))
    (normalSquare : (r : ℕ) → IsPullback (normalComparison r).left
      (@normalProjection S Z' X' q' i' _
        (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
          (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
          square V) r (D'.normalModel r) (D'.normalModelSpec r)).left
      (@normalProjection S Z X q i _ V r
        (D.normalModel r) (D.normalModelSpec r)).left
      (rankBaseChangeSource q p q' p' i hi i' hi' g f square V r).left)
    (cone_normal : (r : ℕ) → coneComparison r ≫ D.coneToNormal r =
      D'.coneToNormal r ≫ normalComparison r) :
    ClosedSpecialization.BaseChange delta q p q' p' i hi i' hi' g f square V D D' where
  deformationComparison := deformationComparison
  deformationIntoPullback := deformationIntoPullback
  deformation_fst := deformation_fst
  deformation_snd := deformation_snd
  deformationClosed := deformationClosed
  infinityComparison := infinityComparison
  infinity_deformation := infinity_deformation
  infinityIntoPullback := infinityIntoPullback
  infinity_fst := infinity_fst
  infinity_snd := infinity_snd
  infinityClosed := infinityClosed
  normalConeComparison := normalConeComparison
  normalConeIntoPullback := normalConeIntoPullback
  normalCone_fst := normalCone_fst
  normalCone_snd := normalCone_snd
  normalConeClosed := normalConeClosed
  normalCone_infinity := normalCone_infinity
  coneComparison := coneComparison
  cone_infinity := cone_infinity
  coneIntoPullback := coneIntoPullback
  cone_fst := cone_fst
  cone_snd := cone_snd
  coneClosed := coneClosed
  normalComparison := normalComparison
  normalSquare := normalSquare
  cone_normal := cone_normal

end BaseChange

end ClosedSpecialization

/-- Canonical rankwise restriction of bivariant classes along a cartesian base change. -/
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
    ClosedSpecialization.RankClass delta q p i hi V r n →+
      ClosedSpecialization.RankClass delta q' p' i' hi'
        (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
          (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
          square V) r n where
  toFun := BivariantClass.restrict delta
    (ClosedSpecialization.rankBaseChangeSource q p q' p' i hi i' hi' g f square V r)
    (@ClosedSpecialization.rankHom S Z' X' q' p' i' hi'
      (IsImmersion.instOfIsClosedImmersion i')
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) r)
    (ClosedSpecialization.topBaseChangeTarget p p' f)
    (ClosedSpecialization.rankBaseChangeSquare q p q' p' i hi i' hi' g f square V r) n
  map_zero' := sorry
  map_add' := sorry

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
    (r : ℕ) (n : ℤ) (c : ClosedSpecialization.RankClass delta q p i hi V r n) :
    rankBaseChange delta q p q' p' i hi i' hi' g f square V r n c =
      BivariantClass.restrict delta
        (ClosedSpecialization.rankBaseChangeSource q p q' p' i hi i' hi' g f square V r)
        (@ClosedSpecialization.rankHom S Z' X' q' p' i' hi'
          (IsImmersion.instOfIsClosedImmersion i')
          (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
            (IsImmersion.instOfIsClosedImmersion i')
            (IsImmersion.instOfIsClosedImmersion i) square V) r)
        (ClosedSpecialization.topBaseChangeTarget p p' f)
        (ClosedSpecialization.rankBaseChangeSquare q p q' p' i hi i' hi' g f square V r) n c :=
  sorry

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
    (D : ClosedSpecialization delta q p i hi V) :
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
  fun r ↦ DirectSum.map (fun n : ℕ ↦
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
    (D : ClosedSpecialization delta q p i hi V) (r : ℕ) :
    closedClassBaseChange delta q p q' p' i hi i' hi' g f square V D r =
      DirectSum.map (fun n : ℕ ↦
        rankBaseChange delta q p q' p' i hi i' hi' g f square V r (n : ℤ))
          (closedClass delta q p i hi V D r) := sorry

/-- Given the source's geometric comparison between the two deformation constructions, the
completed closed class of the pulled virtual normal bundle is the canonical bivariant
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
    (D : ClosedSpecialization delta q p i hi V)
    (D' : ClosedSpecialization delta q' p' i' hi'
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V))
    (comparison : ClosedSpecialization.BaseChange delta q p q' p' i hi i' hi'
      g f square V D D') :
    closedClass delta q' p' i' hi'
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) D' =
      closedClassBaseChange delta q p q' p' i hi i' hi' g f square V D := sorry

namespace ClosedSpecialization

/-- The virtual-normal rank opens cover the source scheme. -/
theorem rankOpen_iSup {Z X : Scheme.{u}} (i : Z ⟶ X) [h_i : IsImmersion i]
    (V : VirtualNormalBundle i) :
    iSup (fun r : ℕ ↦ @rankOpen Z X i h_i V r) = ⊤ := sorry

/-- Distinct virtual-normal rank opens are disjoint. -/
theorem rankOpen_pairwiseDisjoint {Z X : Scheme.{u}} (i : Z ⟶ X)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) :
    Pairwise (fun r s : ℕ ↦
      Disjoint (@rankOpen Z X i h_i V r : Set Z) (@rankOpen Z X i h_i V s : Set Z)) := sorry

/-- Every virtual-normal rank open is clopen. -/
theorem rankOpen_isClopen {Z X : Scheme.{u}} (i : Z ⟶ X) [h_i : IsImmersion i]
    (V : VirtualNormalBundle i) (r : ℕ) :
    IsClopen (@rankOpen Z X i h_i V r : Set Z) := sorry

/-- The one-element family of top opens covers its scheme. -/
theorem unitTop_iSup (X : Scheme.{u}) : iSup (fun _ : Unit ↦ (⊤ : X.Opens)) = ⊤ := sorry

/-- The one-element family of top opens is pairwise disjoint. -/
theorem unitTop_pairwiseDisjoint (X : Scheme.{u}) :
    Pairwise (fun _ _ : Unit ↦ Disjoint ((⊤ : X.Opens) : Set X) ((⊤ : X.Opens) : Set X)) :=
  sorry

/-- The top open of a scheme is clopen. -/
theorem unitTop_isClopen (X : Scheme.{u}) (_ : Unit) : IsClopen ((⊤ : X.Opens) : Set X) := sorry

end ClosedSpecialization

/-- The global degree-`r` class obtained by gluing the completed rank-locus components. -/
noncomputable def globalClassOfRank
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V) (r : ℕ) :
    BivariantClass delta (overHom q p i hi) (r : ℤ) :=
  ((BivariantClass.OpenRestriction.Completion.globalEquiv delta
    (overHom q p i hi) (fun n : ℕ ↦ @rankOpen
      Z X i (inferInstance : IsImmersion i) V n) (fun _ : Unit ↦ ⊤)
    (fun _ ↦ Unit.unit) (ClosedSpecialization.rankOpen_iSup i V)
    (ClosedSpecialization.unitTop_iSup X) (ClosedSpecialization.rankOpen_pairwiseDisjoint i V)
    (ClosedSpecialization.unitTop_pairwiseDisjoint X)
    (ClosedSpecialization.rankOpen_isClopen i V) (ClosedSpecialization.unitTop_isClopen X)
    (fun n ↦ rankOpen_le_preimage_top q p i hi V n))
      (closedClass delta q p i hi V D)).1 r

/-- Restricting `globalClassOfRank` to the rank loci recovers the degree-`r` component of
the completed class. -/
theorem globalClassOfRank_component
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V) (r : ℕ) :
    globalClassOfRank delta q p i hi V D r =
      ((BivariantClass.OpenRestriction.Completion.globalEquiv delta
        (overHom q p i hi)
        (fun n : ℕ ↦ @rankOpen Z X i
          (inferInstance : IsImmersion i) V n) (fun _ : Unit ↦ ⊤)
        (fun _ ↦ Unit.unit) (ClosedSpecialization.rankOpen_iSup i V)
        (ClosedSpecialization.unitTop_iSup X)
        (ClosedSpecialization.rankOpen_pairwiseDisjoint i V)
        (ClosedSpecialization.unitTop_pairwiseDisjoint X)
        (ClosedSpecialization.rankOpen_isClopen i V) (ClosedSpecialization.unitTop_isClopen X)
        (fun n ↦ rankOpen_le_preimage_top q p i hi V n))
          (closedClass delta q p i hi V D)).1 r := sorry

/-- If the virtual normal bundle has constant rank `r`, the completed class is the
completion of its single global homogeneous degree-`r` class. -/
theorem closedClass_eq_completeOfRank
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedSpecialization delta q p i hi V) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r V.module] :
    closedClass delta q p i hi V D =
      BivariantClass.OpenRestriction.Completion.complete delta
        (overHom q p i hi)
        (fun n : ℕ ↦ @rankOpen Z X i
          (inferInstance : IsImmersion i) V n)
        (fun _ : Unit ↦ ⊤) (fun _ ↦ Unit.unit)
        (fun n ↦ rankOpen_le_preimage_top q p i hi V n)
        (DirectSum.of
          (fun n : ℕ ↦ BivariantClass delta (overHom q p i hi) (n : ℤ))
          r (globalClassOfRank delta q p i hi V D r)) := sorry

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
