/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

open MonoidalCategory MonObj CartesianMonoidalCategory

universe u

namespace GroupScheme

/-- The multiplication morphism of a group object whose structure morphism is universally open
is universally open. -/
instance instUniversallyOpenMul {S : Scheme} (G : Over S) [GrpObj G]
    [UniversallyOpen G.hom] : UniversallyOpen (μ[G].left) := sorry

/-- The multiplication map of a group scheme over a field is open. -/
theorem isOpenMap_mul {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G] :
    IsOpenMap (μ[G].left) :=
  Scheme.Hom.isOpenMap (μ[G].left)

/-- Left multiplication by a `T`-valued point of a group scheme is an open map on `T ×_k G`. -/
lemma isOpenMap_mulAlong {k : Type u} [Field k] (G T : SchemeOverField k) [GrpObj G]
    (ψ : T ⟶ G) : IsOpenMap ((((ψ ⊗ₘ 𝟙 G) ≫ μ[G]).left).base) := by
  let e : T ⊗ G ≅ T ⊗ G := {
    hom := lift (fst T G) ((fst T G ≫ ψ) * snd T G)
    inv := lift (fst T G) ((fst T G ≫ ψ)⁻¹ * snd T G)
    hom_inv_id := by
      -- Compare both composites on the pullback projections.
      apply CartesianMonoidalCategory.hom_ext
      · simp
      · set f : T ⊗ G ⟶ G := fst T G ≫ ψ
        simp only [Category.assoc, lift_snd]
        rw [MonObj.comp_mul]
        have hfinv : lift (fst T G) (f * snd T G) ≫ f⁻¹ = f⁻¹ := by
          simp [GrpObj.comp_inv, f]
        have hsnd : lift (fst T G) (f * snd T G) ≫ snd T G = f * snd T G := by
          simp [f]
        rw [hfinv, hsnd]
        simp [f]
    inv_hom_id := by
      -- The inverse uses the same projectionwise computation.
      apply CartesianMonoidalCategory.hom_ext
      · simp
      · set f : T ⊗ G ⟶ G := fst T G ≫ ψ
        simp only [Category.assoc, lift_snd]
        rw [MonObj.comp_mul]
        have hf : lift (fst T G) (f⁻¹ * snd T G) ≫ f = f := by
          simp [f]
        have hsnd : lift (fst T G) (f⁻¹ * snd T G) ≫ snd T G = f⁻¹ * snd T G := by
          simp [f]
        rw [hf, hsnd]
        simp [f] }
  have htensor : ψ ▷ G = lift (fst T G ≫ ψ) (snd T G) := by
    -- Normalize the tensor map to the pullback lift spelling.
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hmul : e.hom ≫ snd T G = (ψ ⊗ₘ 𝟙 G) ≫ μ[G] := by
    -- After the normalization, multiplication is just the second projection after `e`.
    calc
      e.hom ≫ snd T G = fst T G ≫ ψ * snd T G := by simp [e]
      _ = lift (fst T G ≫ ψ) (snd T G) ≫ μ[G] := rfl
      _ = (ψ ⊗ₘ 𝟙 G) ≫ μ[G] := by
        change lift (fst T G ≫ ψ) (snd T G) ≫ μ[G] = (ψ ▷ G) ≫ μ[G]
        simpa using congrArg (fun f ↦ f ≫ μ[G]) htensor.symm
  let e' := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  have hmul_left : e'.hom ≫ (snd T G).left = (((ψ ⊗ₘ 𝟙 G) ≫ μ[G]).left) := by
    -- Forgetting from `Over` transports the equality to the underlying scheme maps.
    simpa [e'] using congrArg Over.Hom.left hmul
  rw [← hmul_left]
  have hOpen : UniversallyOpen (e'.hom ≫ (snd T G).left) := by
    -- Universally openness is invariant under precomposition by an isomorphism.
    rw [MorphismProperty.cancel_left_of_respectsIso @UniversallyOpen e'.hom (snd T G).left]
    change UniversallyOpen (Limits.pullback.snd T.hom G.hom)
    infer_instance
  exact Scheme.Hom.isOpenMap (e'.hom ≫ (snd T G).left)

/-- The morphism `T ×_k U ⟶ T ×_k G` induced by an open subscheme `U ⊆ G` is an open
immersion. -/
lemma isOpenImmersion_tensorRight_openSubscheme {k : Type u} [Field k]
    (T G : SchemeOverField k) (U : G.left.Opens) :
    IsOpenImmersion
      (((𝟙 T) ⊗ₘ (Over.homMk U.ι : Over.mk (U.ι ≫ G.hom) ⟶ G)).left) := by
  -- This map is the base change of `U.ι` along `T.hom`.
  have hfst : T.hom ≫ 𝟙 (Spec (CommRingCat.of k)) = (𝟙 T.left) ≫ T.hom := by
    simp
  have hsnd : (U.ι ≫ G.hom) ≫ 𝟙 (Spec (CommRingCat.of k)) = U.ι ≫ G.hom := by
    simp
  change IsOpenImmersion
    (Limits.pullback.map T.hom (U.ι ≫ G.hom) T.hom G.hom (𝟙 T.left) U.ι
      (𝟙 (Spec (CommRingCat.of k))) hfst hsnd)
  infer_instance

/-- For an open subscheme `U` of a group scheme `G` over a field `k`, the image of
`T ×_k U` in `G` under multiplication by a morphism `f : T ⟶ G` is open. -/
theorem isOpen_range_mul_open {k : Type u} [Field k]
    (G : SchemeOverField k) [GrpObj G] {T : Scheme.{u}} (f : T ⟶ G.left)
    (U : G.left.Opens) :
    let TOver : SchemeOverField k := Over.mk (f ≫ G.hom)
    let fOver : TOver ⟶ G := Over.homMk f
    let UOver : SchemeOverField k := Over.mk (U.ι ≫ G.hom)
    let uOver : UOver ⟶ G := Over.homMk U.ι
    IsOpen (Set.range (((fOver ⊗ₘ uOver) ≫ μ[G]).left.base)) := by
  let TOver : SchemeOverField k := Over.mk (f ≫ G.hom)
  let fOver : TOver ⟶ G := Over.homMk f
  let UOver : SchemeOverField k := Over.mk (U.ι ≫ G.hom)
  let uOver : UOver ⟶ G := Over.homMk U.ι
  let iTU : (TOver ⊗ UOver) ⟶ (TOver ⊗ G) := (𝟙 TOver) ⊗ₘ uOver
  let mT : (TOver ⊗ G) ⟶ G := (fOver ⊗ₘ 𝟙 G) ≫ μ[G]
  change IsOpen (Set.range (((fOver ⊗ₘ uOver) ≫ μ[G]).left.base))
  -- First show that translated multiplication on `T ×_k G` is an open map.
  have hmT : IsOpenMap (mT.left.base) := by
    dsimp [mT]
    simpa [fOver] using isOpenMap_mulAlong G TOver fOver
  -- Next identify `T ×_k U ⟶ T ×_k G` as a pullback open immersion.
  have hiTU : IsOpenImmersion iTU.left := by
    dsimp [iTU]
    simpa [UOver, uOver] using isOpenImmersion_tensorRight_openSubscheme TOver G U
  have hRangeOpen : IsOpen (Set.range iTU.left.base) := by
    -- The image of an open immersion is an open subset.
    simpa using (IsOpenImmersion.isOpen_range iTU.left)
  have hcomp : iTU ≫ mT = ((fOver ⊗ₘ uOver) ≫ μ[G]) := by
    -- Restricting translated multiplication along `T ×_k U ⟶ T ×_k G` recovers the target map.
    calc
      iTU ≫ mT = ((𝟙 TOver ⊗ₘ uOver) ≫ (fOver ⊗ₘ 𝟙 G)) ≫ μ[G] := by
        rfl
      _ = ((𝟙 TOver ≫ fOver) ⊗ₘ (uOver ≫ 𝟙 G)) ≫ μ[G] := by
        rw [tensorHom_comp_tensorHom]
      _ = ((fOver ⊗ₘ uOver) ≫ μ[G]) := by
        simp
  have hRangeImage :
      Set.range (((fOver ⊗ₘ uOver) ≫ μ[G]).left.base) =
        mT.left.base '' Set.range iTU.left.base := by
    -- Rewrite the range of the composite as the image of the open subset `range iTU.left.base`.
    rw [← hcomp]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨iTU.left.base y, ⟨y, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, rfl⟩
  -- Finally, the image of that open subset under the open map `mT` is open.
  rw [hRangeImage]
  exact hmT _ hRangeOpen

/-- The identity point belongs to the pointwise range of a group-scheme homomorphism. -/
lemma rangeContainsIdentity {k : Type u} [Field k]
    {G' G : SchemeOverField k} [GrpObj G'] [GrpObj G]
    (ψ : G' ⟶ G) [IsMonHom ψ] :
    η[G].left (IsLocalRing.closedPoint k) ∈ Set.range ψ.left.base := by
  -- Evaluate the unit-compatibility of `ψ` at the unique point of `Spec k`.
  refine ⟨η[G'].left (IsLocalRing.closedPoint k), ?_⟩
  have hη :
      η[G'].left ≫ ψ.left = η[G].left := by
    exact (congrArg Over.Hom.left (IsMonHom.one_hom (f := ψ)) :
      η[G'].left ≫ ψ.left = η[G].left)
  change (η[G'].left ≫ ψ.left) (IsLocalRing.closedPoint k) =
      η[G].left (IsLocalRing.closedPoint k)
  exact congrArg (fun f ↦ f (IsLocalRing.closedPoint k)) hη

/-- Inversion preserves the pointwise range of a group-scheme homomorphism. -/
lemma rangeInvClosed {k : Type u} [Field k]
    {G' G : SchemeOverField k} [GrpObj G'] [GrpObj G]
    (ψ : G' ⟶ G) [IsMonHom ψ] {y : G.left}
    (hy : y ∈ Set.range ψ.left.base) :
    ι[G].left y ∈ Set.range ψ.left.base := by
  -- Rewrite the inverse using compatibility of `ψ` with the group inverse.
  rcases hy with ⟨y', rfl⟩
  refine ⟨ι[G'].left y', ?_⟩
  have hι :
      ι[G'].left ≫ ψ.left = ψ.left ≫ ι[G].left := by
    exact (congrArg Over.Hom.left (CategoryTheory.GrpObj.inv_hom (f := ψ)) :
      ι[G'].left ≫ ψ.left = ψ.left ≫ ι[G].left)
  change (ι[G'].left ≫ ψ.left) y' = (ψ.left ≫ ι[G].left) y'
  exact congrArg (fun f ↦ f y') hι

/-- The range of the unit section is contained in the pointwise range of a group-scheme
homomorphism. -/
lemma unitRangeSubset_openRange {k : Type u} [Field k]
    {G' G : SchemeOverField k} [GrpObj G'] [GrpObj G]
    (ψ : G' ⟶ G) [IsMonHom ψ] :
    Set.range η[G].left.base ⊆ Set.range ψ.left.base := by
  intro x hx
  rcases hx with ⟨t, rfl⟩
  change Spec (CommRingCat.of k) at t
  have ht : t = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  simpa [ht] using rangeContainsIdentity (k := k) (ψ := ψ)

/-- If the range of a group-scheme homomorphism is open, the constant identity section from the
residue field at any point lifts through the corresponding open subscheme. -/
lemma constantIdentityLiftExists {k : Type u} [Field k]
    {G' G : SchemeOverField k} [GrpObj G'] [GrpObj G]
    (ψ : G' ⟶ G) [IsMonHom ψ] (hψ : IsOpen (Set.range ψ.left.base)) (z : G.left) :
    let U : G.left.Opens := ⟨Set.range ψ.left.base, hψ⟩
    let TOver : SchemeOverField k := Over.mk (G.left.fromSpecResidueField z ≫ G.hom)
    let UOver : SchemeOverField k := Over.mk (U.ι ≫ G.hom)
    let uOver : UOver ⟶ G := Over.homMk U.ι
    ∃ e : TOver ⟶ UOver, e ≫ uOver = toUnit TOver ≫ η[G] := by
  let U : G.left.Opens := ⟨Set.range ψ.left.base, hψ⟩
  let TOver : SchemeOverField k := Over.mk (G.left.fromSpecResidueField z ≫ G.hom)
  let UOver : SchemeOverField k := Over.mk (U.ι ≫ G.hom)
  let uOver : UOver ⟶ G := Over.homMk U.ι
  -- The constant unit section lands in the open range because the unit itself already does.
  have hUnitRange :
      Set.range ((toUnit TOver ≫ η[G]).left.base) ⊆ Set.range U.ι := by
    intro x hx
    rcases hx with ⟨t, rfl⟩
    have hxEta :
        ((toUnit TOver ≫ η[G]).left) t ∈ Set.range η[G].left.base := by
      refine ⟨(toUnit TOver).left t, rfl⟩
    have hxRange :
        ((toUnit TOver ≫ η[G]).left) t ∈ Set.range ψ.left.base :=
      unitRangeSubset_openRange (k := k) (ψ := ψ) hxEta
    exact ⟨⟨((toUnit TOver ≫ η[G]).left) t, hxRange⟩, rfl⟩
  let eLeft : TOver.left ⟶ UOver.left :=
    @IsOpenImmersion.lift _ _ _ U.ι ((toUnit TOver ≫ η[G]).left)
      (Scheme.Opens.instIsOpenImmersionι U) hUnitRange
  have heLeft_fac : eLeft ≫ uOver.left = (toUnit TOver ≫ η[G]).left := by
    simpa [eLeft, uOver] using
      (@IsOpenImmersion.lift_fac _ _ _ U.ι ((toUnit TOver ≫ η[G]).left)
        (Scheme.Opens.instIsOpenImmersionι U) hUnitRange)
  have heLeft_over : eLeft ≫ UOver.hom = TOver.hom := by
    -- The lifted map remains over `Spec k` because the unit morphism is over the base.
    calc
      eLeft ≫ UOver.hom = eLeft ≫ uOver.left ≫ G.hom := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ eLeft ≫ k) (Over.w uOver).symm
      _ = (toUnit TOver ≫ η[G]).left ≫ G.hom := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ G.hom) heLeft_fac
      _ = TOver.hom := by simpa using (Over.w (toUnit TOver ≫ η[G]))
  refine ⟨Over.homMk eLeft heLeft_over, ?_⟩
  -- Forgetting to underlying schemes identifies the composite with the constant unit section.
  apply Over.OverMorphism.ext
  exact heLeft_fac

/-- A morphism of group schemes commutes with the categorical difference map. -/
lemma mapDifference_eq {k : Type u} [Field k]
    {G' G : SchemeOverField k} [GrpObj G'] [GrpObj G]
    (ψ : G' ⟶ G) [IsMonHom ψ] :
    (ψ ⊗ₘ ψ) ≫ (lift (fst G G) (snd G G ≫ ι[G]) ≫ μ[G]) =
      (lift (fst G' G') (snd G' G' ≫ ι[G']) ≫ μ[G']) ≫ ψ := by
  -- Normalize the tensor and inverse expressions, then use compatibility with multiplication
  -- and inversion.
  sorry

/-- If the pointwise range of a morphism of group schemes over a field is open, then it is
closed. -/
theorem isClosed_range_of_isOpen {k : Type u} [Field k]
    {G' G : SchemeOverField k} [GrpObj G'] [GrpObj G]
    (ψ : G' ⟶ G) [IsMonHom ψ] (hψ : IsOpen (Set.range ψ.left.base)) :
    IsClosed (Set.range ψ.left.base) := by
  -- Work with translated open neighborhoods of complement points.
  let U : G.left.Opens := ⟨Set.range ψ.left.base, hψ⟩
  -- It suffices to show that the complement is open via translated open neighborhoods.
  have hComplOpen : IsOpen (Set.range ψ.left.base)ᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    let TOver : SchemeOverField k := Over.mk (G.left.fromSpecResidueField z ≫ G.hom)
    let fOver : TOver ⟶ G := Over.homMk (G.left.fromSpecResidueField z)
    let UOver : SchemeOverField k := Over.mk (U.ι ≫ G.hom)
    let uOver : UOver ⟶ G := Over.homMk U.ι
    let V : Set G.left := Set.range ((((fOver ⊗ₘ uOver) ≫ μ[G]).left).base)
    have hVOpen : IsOpen V := by
      -- The translated image of the open range is open.
      simpa [TOver, fOver, UOver, uOver, V] using
        (isOpen_range_mul_open G (G.left.fromSpecResidueField z) U)
    have hBaseRangeSubset : Set.range fOver.left.base ⊆ V := by
      -- The identity lift shows that translated multiplication contains the entire image of
      -- `Spec κ(z) ⟶ G`.
      rcases constantIdentityLiftExists (k := k) (ψ := ψ) hψ z with ⟨e, he⟩
      have hSection :
          lift (𝟙 TOver) e ≫ ((fOver ⊗ₘ uOver) ≫ μ[G]) = fOver := by
        -- Multiplication by the lifted identity section is the identity on the first factor.
        have hLiftMap :
            lift (𝟙 TOver) e ≫ (fOver ⊗ₘ uOver) =
              lift (𝟙 TOver ≫ fOver) (e ≫ uOver) := by
          simpa using lift_map (𝟙 TOver) e fOver uOver
        calc
          lift (𝟙 TOver) e ≫ ((fOver ⊗ₘ uOver) ≫ μ[G]) =
              (lift (𝟙 TOver) e ≫ (fOver ⊗ₘ uOver)) ≫ μ[G] := by
                simp
          _ = lift (𝟙 TOver ≫ fOver) (e ≫ uOver) ≫ μ[G] := by rw [hLiftMap]
          _ = lift fOver (toUnit TOver ≫ η[G]) ≫ μ[G] := by
                rw [Category.id_comp, he]
          _ = fOver := by
                simpa using
                  (CategoryTheory.MonObj.lift_comp_one_right
                    (B := G) (f := fOver) (g := toUnit TOver))
      have hSection_left :
          (lift (𝟙 TOver) e ≫ ((fOver ⊗ₘ uOver) ≫ μ[G])).left = fOver.left :=
        congrArg Over.Hom.left hSection
      intro x hx
      rcases hx with ⟨t, ht⟩
      refine ⟨(lift (𝟙 TOver) e).left t, ?_⟩
      -- Evaluating the section identity at `t` produces the required witness in `V`.
      have hEval := congrArg (fun f : TOver.left ⟶ G.left ↦ f t) hSection_left
      change (((fOver ⊗ₘ uOver) ≫ μ[G]).left ((lift (𝟙 TOver) e).left t)) = fOver.left t at hEval
      exact hEval.trans ht
    have hzBase : z ∈ Set.range fOver.left.base := by
      -- The residue-field point map hits `z` at the unique closed point of `Spec κ(z)`.
      refine ⟨IsLocalRing.closedPoint (G.left.residueField z), ?_⟩
      change G.left.fromSpecResidueField z (IsLocalRing.closedPoint (G.left.residueField z)) = z
      exact Scheme.fromSpecResidueField_apply z _
    have hzV : z ∈ V := hBaseRangeSubset hzBase
    have hTensorMap :
        (fOver ⊗ₘ uOver) =
          lift (fst TOver UOver ≫ fOver) (snd TOver UOver ≫ uOver) := by
      -- The tensor product map is the pullback lift of the two component maps.
      calc
        (fOver ⊗ₘ uOver) = 𝟙 (TOver ⊗ UOver) ≫ (fOver ⊗ₘ uOver) := by simp
        _ = lift (fst TOver UOver) (snd TOver UOver) ≫ (fOver ⊗ₘ uOver) := by
              rw [lift_fst_snd]
        _ = lift (fst TOver UOver ≫ fOver) (snd TOver UOver ≫ uOver) := by
              simpa using lift_map (fst TOver UOver) (snd TOver UOver) fOver uOver
    have translatedNeighborhood_cancelRight_over :
        lift ((fOver ⊗ₘ uOver) ≫ μ[G]) ((snd TOver UOver ≫ uOver) ≫ ι[G]) ≫ μ[G] =
          fst TOver UOver ≫ fOver := by
      -- Cancel the `U`-factor once at the morphism level before evaluating at points.
      rw [CategoryTheory.GrpObj.lift_inv_right_eq]
      have hTranslated :
          ((fOver ⊗ₘ uOver) ≫ μ[G]) =
            lift (fst TOver UOver ≫ fOver) (snd TOver UOver ≫ uOver) ≫ μ[G] := by
        rw [hTensorMap]
      simpa [Category.assoc] using hTranslated
    have translatedNeighborhood_cancelRight :
        (lift ((fOver ⊗ₘ uOver) ≫ μ[G]) ((snd TOver UOver ≫ uOver) ≫ ι[G]) ≫ μ[G]).left =
          Limits.pullback.fst TOver.hom UOver.hom ≫ fOver.left := by
      -- Forgetting the over-category cancellation identity gives the scheme-level bridge.
      simpa [Category.assoc] using
        congrArg Over.Hom.left translatedNeighborhood_cancelRight_over
    have translatedFirstProjection_eq_basePoint (p : (TOver ⊗ UOver).left) :
        fOver.left (Limits.pullback.fst TOver.hom UOver.hom p) = z := by
      -- The structure map from `Spec κ(z)` sends every point to `z`.
      change G.left.fromSpecResidueField z (Limits.pullback.fst TOver.hom UOver.hom p) = z
      simpa [fOver] using
        (Scheme.fromSpecResidueField_apply z (Limits.pullback.fst TOver.hom UOver.hom p))
    have hVDisjoint : V ⊆ (Set.range ψ.left.base)ᶜ := by
      -- Any point in the translated neighborhood has a second projection already lying in the
      -- original range, because `UOver.left` is the open subscheme cut out by that range.
      have translatedSecondProjection_memRange (p : (TOver ⊗ UOver).left) :
          ((snd TOver UOver ≫ uOver).left p) ∈ Set.range ψ.left.base := by
        -- The second projection lands in `U`, and `U` was defined to be the range of `ψ`.
        have hInU :
            ((snd TOver UOver ≫ uOver).left p) ∈ Set.range U.ι := by
          refine ⟨Limits.pullback.snd TOver.hom UOver.hom p, ?_⟩
          rfl
        simpa [U] using hInU
      intro w hwV
      rw [Set.mem_compl_iff]
      intro hwRange
      rcases hwV with ⟨p, rfl⟩
      have hsecondRange :
          ((snd TOver UOver ≫ uOver).left p) ∈ Set.range ψ.left.base :=
        translatedSecondProjection_memRange p
      have hcancelRange :
          (lift ((fOver ⊗ₘ uOver) ≫ μ[G]) ((snd TOver UOver ≫ uOver) ≫ ι[G]) ≫ μ[G]).left p ∈
            Set.range ψ.left.base := by
        -- Transport the two range witnesses through the difference map and identify the result
        -- with the cancellation point by normalizing the pullback witnesses.
        sorry
      have hcancelEval :
          (lift ((fOver ⊗ₘ uOver) ≫ μ[G]) ((snd TOver UOver ≫ uOver) ≫ ι[G]) ≫ μ[G]).left p =
            fOver.left (Limits.pullback.fst TOver.hom UOver.hom p) := by
        -- Evaluate the previously established cancellation identity at the chosen witness.
        exact congrArg (fun f : (TOver ⊗ UOver).left ⟶ G.left ↦ f p)
          translatedNeighborhood_cancelRight
      have hzEq :
          z =
            (lift ((fOver ⊗ₘ uOver) ≫ μ[G]) ((snd TOver UOver ≫ uOver) ≫ ι[G]) ≫
              μ[G]).left p := by
        -- The cancellation value is the base point `z` after rewriting the first projection.
        calc
          z = fOver.left (Limits.pullback.fst TOver.hom UOver.hom p) := by
                symm
                exact translatedFirstProjection_eq_basePoint p
          _ = (lift ((fOver ⊗ₘ uOver) ≫ μ[G]) ((snd TOver UOver ≫ uOver) ≫ ι[G]) ≫
                μ[G]).left p := by
                symm
                exact hcancelEval
      have hzRange' : z ∈ Set.range ψ.left.base := by
        simpa [hzEq] using hcancelRange
      exact hz hzRange'
    exact Filter.mem_of_superset (hVOpen.mem_nhds hzV) hVDisjoint
  rw [← isOpen_compl_iff]
  exact hComplOpen

/-- If the pointwise range of a morphism of group schemes over a field is open, then it is
clopen. -/
theorem isClopen_range_of_isOpen {k : Type u} [Field k]
    {G' G : SchemeOverField k} [GrpObj G'] [GrpObj G]
    (ψ : G' ⟶ G) [IsMonHom ψ] (hψ : IsOpen (Set.range ψ.left.base)) :
    IsClopen (Set.range ψ.left.base) :=
  ⟨isClosed_range_of_isOpen ψ hψ, hψ⟩

end GroupScheme

end AlgebraicGeometry
