/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.GroupScheme.Reduction
public import ReasLib.AlgebraicGeometry.GroupScheme.Subgroup.Factorization
public import ReasLib.AlgebraicGeometry.GroupScheme.Topology
public import ReasLib.AlgebraicGeometry.Scheme.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.Product
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Immersion.SchemeTheoreticImage
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Product
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Subset
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.UniversalHomeomorphism

/-!
# Immersions of group schemes over fields

An immersion between group schemes over a field is a closed immersion. The proof passes to an
algebraic closure and analyzes the scheme-theoretic image of the reduced source.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.GroupScheme

/-- Field-extension base change identifies the preimage of a morphism's set-theoretic range with
the range of the base-changed morphism. -/
private theorem baseChange_preimage_range_eq_range
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G' G : SchemeOverField k} (i : G' ⟶ G) :
    (FieldExtension.Over.toSource k K G) ⁻¹' Set.range i.left =
      Set.range (((FieldExtension.Over.functor k K).map i).left) := by
  change (Limits.pullback.fst G.hom (FieldExtension.specMap k K)) ⁻¹' Set.range i.left =
    Set.range
      (Limits.pullback.map G'.hom (FieldExtension.specMap k K) G.hom
        (FieldExtension.specMap k K) i.left (𝟙 _) (𝟙 _)
        (by simpa using Over.w i) (by simp))
  symm
  simpa [Set.range_id, Set.inter_eq_left] using
    (Scheme.Pullback.range_map G'.hom (FieldExtension.specMap k K) G.hom
      (FieldExtension.specMap k K) i.left (𝟙 _) (𝟙 _) (by simp) (by simp))

/-- The projection from a field-extension base change is a quotient map. -/
private theorem baseChange_toSource_isQuotientMap
    {k K : Type u} [Field k] [Field K] [Algebra k K] (X : SchemeOverField k) :
    Topology.IsQuotientMap (FieldExtension.Over.toSource k K X) := by
  change Topology.IsQuotientMap (FieldExtension.toSource k K X.hom)
  simpa [FieldExtension.Over.toSource] using
    (Flat.isQuotientMap_of_surjective (f := FieldExtension.toSource k K X.hom))

/-- The canonical scheme-theoretic image of a morphism from a reduced scheme is reduced. -/
private theorem imageOver_isReduced
    {k : Type u} [Field k] {G' G : SchemeOverField k} [IsReduced G'.left]
    (i : G' ⟶ G) : IsReduced (Scheme.Hom.imageOver i).left := by
  change IsReduced i.left.image
  rw [Scheme.Hom.image_eq_vanishingIdeal_subscheme_closure_range_of_isReduced i.left]
  infer_instance

/-- For a morphism from a reduced scheme, the range of its canonical image inclusion is the
closure of the original set-theoretic range. -/
private theorem range_imageιOver_eq_closure_range
    {k : Type u} [Field k] {G' G : SchemeOverField k} [IsReduced G'.left]
    (i : G' ⟶ G) :
    Set.range (Scheme.Hom.imageιOver i).left = closure (Set.range i.left) := by
  calc
    Set.range (Scheme.Hom.imageιOver i).left = (i.left.ker.support : Set G.left) := by
      change Set.range i.left.imageι = (i.left.ker.support : Set G.left)
      rw [Scheme.IdealSheafData.range_subschemeι]
    _ = closure (Set.range i.left) := by
      rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range_of_isReduced i.left,
        Scheme.IdealSheafData.support_vanishingIdeal]
      rfl

/-- Multiplication in a group scheme preserves the closed image of an immersion from a reduced
group scheme over a perfect field. -/
private theorem imageOver_mul_range_subset
    {k : Type u} [Field k] [PerfectField k]
    {G' G : SchemeOverField k} [GrpObj G'] [GrpObj G] [IsReduced G'.left]
    (i : G' ⟶ G) [IsMonHom i] [IsImmersion i.left] :
    Set.range ((((Scheme.Hom.imageιOver i) ⊗ₘ (Scheme.Hom.imageιOver i)) ≫ μ[G]).left) ⊆
      Set.range (Scheme.Hom.imageιOver i).left := by
  let I := Scheme.Hom.imageOver i
  let j : I ⟶ G := Scheme.Hom.imageιOver i
  have hRangej : Set.range j.left = closure (Set.range i.left) := by
    simpa [I, j] using range_imageιOver_eq_closure_range (i := i)
  have hjMapsTo :
      Set.MapsTo j.left (Set.univ : Set I.left) (closure (Set.range i.left)) := by
    intro x hx
    have hxRange : j.left x ∈ Set.range j.left := ⟨x, rfl⟩
    simpa [hRangej] using hxRange
  have hTensorMaps :
      Set.MapsTo ((j ⊗ₘ j).left)
        (Scheme.Pullback.subset I.hom I.hom (Set.univ : Set I.left) Set.univ)
        (Scheme.Pullback.subset G.hom G.hom
          (closure (Set.range i.left)) (closure (Set.range i.left))) := by
    change Set.MapsTo
      (Limits.pullback.map I.hom I.hom G.hom G.hom j.left j.left (𝟙 _)
        (by simpa using (Over.w j).symm) (by simpa using (Over.w j).symm))
      (Scheme.Pullback.subset I.hom I.hom (Set.univ : Set I.left) Set.univ)
      (Scheme.Pullback.subset G.hom G.hom
        (closure (Set.range i.left)) (closure (Set.range i.left)))
    exact
      Scheme.Pullback.map_mapsTo_subset_of_mapsTo
        I.hom I.hom G.hom G.hom j.left j.left (𝟙 _)
        (by simpa using (Over.w j).symm) (by simpa using (Over.w j).symm)
        (Set.univ : Set I.left) Set.univ
        (closure (Set.range i.left)) (closure (Set.range i.left))
        hjMapsTo hjMapsTo
  have hTensorRange :
      Set.range ((j ⊗ₘ j).left) ⊆ closure (Set.range ((i ⊗ₘ i).left)) := by
    intro x hx
    rcases hx with ⟨p, rfl⟩
    have hp :
        p ∈ Scheme.Pullback.subset I.hom I.hom (Set.univ : Set I.left) Set.univ := by
      simp [Scheme.Pullback.mem_subset_iff]
    have hp' := hTensorMaps hp
    have hClosureTensor :
        Scheme.Pullback.subset G.hom G.hom
            (closure (Set.range i.left)) (closure (Set.range i.left)) =
          closure (Set.range ((i ⊗ₘ i).left)) := by
      exact Scheme.Pullback.subset_closure_range_eq_closure_range_tensor (f := i) (g := i)
    exact hClosureTensor ▸ hp'
  have hMulMaps :
      Set.MapsTo μ[G].left (Set.range ((i ⊗ₘ i).left)) (Set.range i.left) := by
    intro x hx
    rcases hx with ⟨p, rfl⟩
    refine ⟨μ[G'].left p, ?_⟩
    have hMul : μ[G'].left ≫ i.left = ((i ⊗ₘ i) ≫ μ[G]).left := by
      exact congrArg Over.Hom.left (IsMonHom.mul_hom (f := i))
    exact congrArg (fun f : (G' ⊗ G').left ⟶ G.left ↦ f p) hMul
  have hMulClosure :
      Set.MapsTo μ[G].left
        (closure (Set.range ((i ⊗ₘ i).left))) (closure (Set.range i.left)) :=
    hMulMaps.closure μ[G].left.continuous
  intro x hx
  rcases hx with ⟨p, rfl⟩
  have hp : (j ⊗ₘ j).left p ∈ closure (Set.range ((i ⊗ₘ i).left)) :=
    hTensorRange ⟨p, rfl⟩
  have hx' : μ[G].left ((j ⊗ₘ j).left p) ∈ closure (Set.range i.left) :=
    hMulClosure hp
  change μ[G].left ((j ⊗ₘ j).left p) ∈ Set.range j.left
  rw [hRangej]
  exact hx'

/-- The canonical closed image inclusion of an immersion of group schemes admits compatible
unit, multiplication, and inverse factorizations. -/
private theorem imageOverFactorization
    {k : Type u} [Field k] [PerfectField k]
    {G' G : SchemeOverField k} [GrpObj G'] [GrpObj G] [IsReduced G'.left]
    (i : G' ⟶ G) [IsMonHom i] [IsImmersion i.left] :
    Nonempty (GrpObj.Factorization (Scheme.Hom.imageιOver i)) := by
  let I := Scheme.Hom.imageOver i
  let j : I ⟶ G := Scheme.Hom.imageιOver i
  -- Local instance justification (proof-local temporary data): the image object is reduced because the source is reduced.
  letI : IsReduced I.left := imageOver_isReduced (i := i)
  -- Local instance justification (proof-local temporary data): products of reduced schemes over the perfect base field are reduced.
  letI : IsReduced (I ⊗ I).left := by
    change IsReduced (Limits.pullback I.hom I.hom : Scheme)
    exact SchemeOverField.isReduced_pullback_of_isReduced_of_perfectField I I
  -- Local instance justification (proof-local temporary data): the spectrum of the base field is reduced for the unit lift.
  letI : IsReduced (Over.left (𝟙_ (SchemeOverField k))) := by
    change IsReduced (Spec (CommRingCat.of k))
    infer_instance
  have hRangej : Set.range j.left = closure (Set.range i.left) := by
    simpa [I, j] using range_imageιOver_eq_closure_range (i := i)
  have hOneRange : Set.range η[G].left ⊆ Set.range j.left := by
    intro x hx
    rcases hx with ⟨t, rfl⟩
    change Spec (CommRingCat.of k) at t
    have ht : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [hRangej]
    have hId : η[G].left (IsLocalRing.closedPoint k) ∈ Set.range i.left := by
      simpa using rangeContainsIdentity (k := k) (ψ := i)
    simpa [ht] using subset_closure hId
  obtain ⟨oneLeft, honeLeft, _⟩ :=
    (AlgebraicGeometry.IsClosedImmersion.existsUnique_lift_iff_range_subset
      j.left η[G].left).2 hOneRange
  let one : 𝟙_ (SchemeOverField k) ⟶ I :=
    Over.homMk oneLeft <| by
      calc
        oneLeft ≫ I.hom = oneLeft ≫ j.left ≫ G.hom := by rfl
        _ = η[G].left ≫ G.hom := by
          simpa [Category.assoc] using congrArg (fun f ↦ f ≫ G.hom) honeLeft
        _ = (𝟙_ (SchemeOverField k)).hom := by simpa using (Over.w η[G])
  have hInvRange : Set.range (j.left ≫ ι[G].left) ⊆ Set.range j.left := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    rw [hRangej]
    have hy : j.left y ∈ closure (Set.range i.left) := by
      simpa [hRangej] using (show j.left y ∈ Set.range j.left from ⟨y, rfl⟩)
    have hInvMaps : Set.MapsTo ι[G].left (Set.range i.left) (Set.range i.left) := by
      intro z hz
      simpa using rangeInvClosed (k := k) (ψ := i) hz
    exact (hInvMaps.closure ι[G].left.continuous) hy
  obtain ⟨invLeft, hinvLeft, _⟩ :=
    (AlgebraicGeometry.IsClosedImmersion.existsUnique_lift_iff_range_subset
      j.left (j.left ≫ ι[G].left)).2 hInvRange
  let inv : I ⟶ I :=
    Over.homMk invLeft <| by
      calc
        invLeft ≫ I.hom = invLeft ≫ j.left ≫ G.hom := by rfl
        _ = (j.left ≫ ι[G].left) ≫ G.hom := by
          simpa [Category.assoc] using congrArg (fun f ↦ f ≫ G.hom) hinvLeft
        _ = I.hom := by simpa [Category.assoc] using (Over.w (j ≫ ι[G]))
  have hMulRange :
      Set.range (((j ⊗ₘ j) ≫ μ[G]).left) ⊆ Set.range j.left := by
    simpa [I, j] using imageOver_mul_range_subset (i := i)
  obtain ⟨mulLeft, hmulLeft, _⟩ :=
    (AlgebraicGeometry.IsClosedImmersion.existsUnique_lift_iff_range_subset
      j.left (((j ⊗ₘ j) ≫ μ[G]).left)).2 hMulRange
  let mul : I ⊗ I ⟶ I :=
    Over.homMk mulLeft <| by
      calc
        mulLeft ≫ I.hom = mulLeft ≫ j.left ≫ G.hom := by rfl
        _ = (((j ⊗ₘ j) ≫ μ[G]).left) ≫ G.hom := by
          simpa [Category.assoc] using congrArg (fun f ↦ f ≫ G.hom) hmulLeft
        _ = (I ⊗ I).hom := by
          simpa [Category.assoc] using (Over.w ((j ⊗ₘ j) ≫ μ[G]))
  refine ⟨{
    one := one
    mul := mul
    inv := inv
    one_hom := ?_
    mul_hom := ?_
    inv_hom := ?_ }⟩
  · apply Over.OverMorphism.ext
    exact honeLeft
  · apply Over.OverMorphism.ext
    exact hmulLeft
  · apply Over.OverMorphism.ext
    exact hinvLeft

/-- An immersion of group schemes from a reduced source over a perfect field has closed
set-theoretic range. -/
private theorem reducedSource_isClosed_range_of_isImmersion
    {k : Type u} [Field k] [PerfectField k]
    {G' G : SchemeOverField k} [GrpObj G'] [GrpObj G] [IsReduced G'.left]
    (i : G' ⟶ G) [IsMonHom i] [IsImmersion i.left] : IsClosed (Set.range i.left) := by
  let I := Scheme.Hom.imageOver i
  let j : I ⟶ G := Scheme.Hom.imageιOver i
  -- Local instance justification (proof-local temporary data): the closed image inclusion is monic while transporting the group structure.
  letI : Mono j := Over.mono_of_mono_left j
  let ti : G' ⟶ I := Scheme.Hom.toImageOver i
  obtain ⟨F⟩ := imageOverFactorization (i := i)
  -- Local instance justification (proof-local temporary data): the image factorization supplies the group structure used in the descent argument.
  letI : GrpObj I := F.toGrpObj
  -- Local instance justification (proof-local temporary data): the image factorization makes its closed inclusion a group homomorphism.
  letI : IsMonHom j := by
    change IsMonHom (F.toHom.hom.hom)
    simpa [CategoryTheory.GrpObj.Factorization.toHom_hom] using
      (inferInstance : IsMonHom (F.toHom.hom.hom))
  have hti_comp : ti ≫ j = i := by
    apply Over.OverMorphism.ext
    change i.left.toImage ≫ i.left.imageι = i.left
    exact i.left.toImage_imageι
  -- Local instance justification (proof-local temporary data): monicity of the image inclusion transports the group-homomorphism laws to the image map.
  letI : IsMonHom ti := by
    refine { one_hom := ?_, mul_hom := ?_ }
    · rw [← cancel_mono j]
      calc
        η[G'] ≫ ti ≫ j = η[G'] ≫ i := by
          simpa [Category.assoc] using congrArg (fun f ↦ η[G'] ≫ f) hti_comp
        _ = η[G] := IsMonHom.one_hom (f := i)
        _ = F.one ≫ j := by
          symm
          exact F.one_hom
        _ = η[I] ≫ j := by rfl
    · rw [← cancel_mono j]
      have hTensorTi : (ti ⊗ₘ ti) ≫ (j ⊗ₘ j) = i ⊗ₘ i := by
        simpa [hti_comp] using
          (MonoidalCategory.tensorHom_comp_tensorHom ti j ti j)
      calc
        μ[G'] ≫ ti ≫ j = μ[G'] ≫ i := by
          simpa [Category.assoc] using congrArg (fun f ↦ μ[G'] ≫ f) hti_comp
        _ = (i ⊗ₘ i) ≫ μ[G] := IsMonHom.mul_hom (f := i)
        _ = ((ti ⊗ₘ ti) ≫ (j ⊗ₘ j)) ≫ μ[G] := by rw [← hTensorTi]
        _ = (ti ⊗ₘ ti) ≫ F.mul ≫ j := by
          simpa [Category.assoc, j] using
            (congrArg (fun f ↦ (ti ⊗ₘ ti) ≫ f) F.mul_hom).symm
        _ = (ti ⊗ₘ ti) ≫ μ[I] ≫ j := by rfl
  -- Local instance justification (proof-local temporary data): the reduced-source image map is an open immersion for the open-range theorem.
  letI : IsOpenImmersion ti.left := by
    change IsOpenImmersion i.left.toImage
    exact Scheme.Hom.isOpenImmersion_toImage_of_quasiCompact_or_isReduced
      i.left (Or.inr inferInstance)
  -- Local instance justification (proof-local temporary data): the reduced-source image map has dense range in its scheme-theoretic image.
  letI : IsDominant ti.left := by
    change IsDominant i.left.toImage
    exact Scheme.Hom.isDominant_toImage_of_quasiCompact_or_isReduced
      i.left (Or.inr inferInstance)
  have hOpenTi : IsOpen (Set.range ti.left) := IsOpenImmersion.isOpen_range ti.left
  have hClosedTi : IsClosed (Set.range ti.left) :=
    isClosed_range_of_isOpen (k := k) (G' := G') (G := I) ti hOpenTi
  have hDenseTi : DenseRange ti.left := Scheme.Hom.denseRange ti.left
  have hRangeTi : Set.range ti.left = Set.univ := by
    simpa [hClosedTi.closure_eq] using (denseRange_iff_closure_range.mp hDenseTi)
  have hti_comp_left : ti.left ≫ j.left = i.left := congrArg Over.Hom.left hti_comp
  have hti_surjective : Function.Surjective ti.left := by
    intro x
    have hx : x ∈ Set.range ti.left := by
      simpa [hRangeTi] using (show x ∈ (Set.univ : Set I.left) from trivial)
    simpa using hx
  have hRangeEq : Set.range i.left = Set.range j.left := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨ti.left y, ?_⟩
      simpa [Category.assoc] using
        congrArg (fun f : G'.left ⟶ G.left ↦ f y) hti_comp_left
    · rintro ⟨y, rfl⟩
      rcases hti_surjective y with ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      simpa [Category.assoc] using
        (congrArg (fun f : G'.left ⟶ G.left ↦ f x) hti_comp_left).symm
  simpa [hRangeEq] using
    (IsClosedImmersion.isClosedEmbedding (f := j.left)).isClosed_range

/-- Precomposing a morphism from a group scheme over a perfect field with the canonical reduction
inclusion does not change its set-theoretic range. -/
private theorem reductionSource_comp_range_eq_range
    {k : Type u} [Field k] [PerfectField k]
    {G' G : SchemeOverField k} [GrpObj G'] [GrpObj G] (i : G' ⟶ G) :
    Set.range (((AlgebraicGeometry.Over.reductionιGrp G').hom.hom ≫ i).left) =
      Set.range i.left := by
  change Set.range (i.left ∘ Scheme.reductionι G'.left) = Set.range i.left
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Scheme.reductionι G'.left x, rfl⟩
  · rintro ⟨x, rfl⟩
    -- Local instance justification (proof-local temporary data): surjectivity of the reduction inclusion supplies a preimage of the chosen point.
    letI : Surjective (Scheme.reductionι G'.left) := Scheme.surjective_reductionι G'.left
    rcases (Scheme.reductionι G'.left).surjective x with ⟨x', rfl⟩
    exact ⟨x', rfl⟩

/-- Over a perfect field, an immersion of group schemes has closed set-theoretic range. -/
private theorem perfectField_isClosed_range_of_isImmersion
    {k : Type u} [Field k] [PerfectField k]
    {G' G : SchemeOverField k} [GrpObj G'] [GrpObj G]
    (i : G' ⟶ G) [IsMonHom i] [IsImmersion i.left] : IsClosed (Set.range i.left) := by
  -- Local instance justification (proof-local temporary data): the canonical reduction is reduced for the reduced-source argument.
  letI : IsReduced (AlgebraicGeometry.Over.reduction G').left := by
    change IsReduced (Scheme.reduction G'.left)
    infer_instance
  let ired : AlgebraicGeometry.Over.reduction G' ⟶ G :=
    (AlgebraicGeometry.Over.reductionιGrp G').hom.hom ≫ i
  -- Local instance justification (proof-local temporary data): the composite of the reduction inclusion with the given immersion is an immersion.
  letI : IsImmersion ired.left := by
    change IsImmersion (Scheme.reductionι G'.left ≫ i.left)
    infer_instance
  have hired : IsClosed (Set.range ired.left) := by
    exact reducedSource_isClosed_range_of_isImmersion
      (k := k) (G' := AlgebraicGeometry.Over.reduction G') (G := G) ired
  have hEq : Set.range ired.left = Set.range i.left := by
    simpa [ired] using
      reductionSource_comp_range_eq_range (k := k) (G' := G') (G := G) i
  rwa [hEq] at hired

/-- An immersion of group schemes over a field is a closed immersion. -/
instance isClosedImmersion_of_isImmersion
    {k : Type u} [Field k] {G' G : SchemeOverField k} [GrpObj G'] [GrpObj G]
    (i : G' ⟶ G) [IsMonHom i] [IsImmersion i.left] : IsClosedImmersion i.left := by
  rw [Scheme.Hom.isClosedImmersion_iff_isClosed_range_of_isImmersion]
  let K := AlgebraicClosure k
  -- Local instance justification (proof-local temporary data): base change transports the group-homomorphism law to the algebraic closure.
  letI : IsMonHom ((FieldExtension.Over.functor k K).map i) := by
    change IsMonHom (((FieldExtension.Over.functor k K).mapGrp.map (Grp.ofHom i)).hom.hom)
    infer_instance
  -- Local instance justification (proof-local temporary data): base change transports the immersion property to the algebraic closure.
  letI : IsImmersion (((FieldExtension.Over.functor k K).map i).left) := by
    change IsImmersion
      (Limits.pullback.map G'.hom (FieldExtension.specMap k K) G.hom
        (FieldExtension.specMap k K) i.left (𝟙 _) (𝟙 _)
        (by simpa using Over.w i) (by simp))
    rw [CategoryTheory.Limits.pullback_map_eq_pullbackFstFstIso_inv]
    infer_instance
  have hclosedK :
      IsClosed (Set.range (((FieldExtension.Over.functor k K).map i).left)) := by
    simpa using
      (perfectField_isClosed_range_of_isImmersion
        (k := K) (G' := FieldExtension.Over.baseChange k K G')
        (G := FieldExtension.Over.baseChange k K G)
        ((FieldExtension.Over.functor k K).map i))
  have hpreimage :
      IsClosed ((FieldExtension.Over.toSource k K G) ⁻¹' Set.range i.left) := by
    simpa [K, baseChange_preimage_range_eq_range
      (k := k) (K := K) (G' := G') (G := G) i] using hclosedK
  have hquot : Topology.IsQuotientMap (FieldExtension.Over.toSource k K G) :=
    baseChange_toSource_isQuotientMap (k := k) (K := K) G
  exact (hquot.isCoinducing.isClosed_preimage).1 hpreimage

end AlgebraicGeometry.GroupScheme
