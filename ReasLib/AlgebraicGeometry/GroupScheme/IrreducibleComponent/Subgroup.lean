module

public import ReasLib.AlgebraicGeometry.GroupScheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.GroupScheme.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.Product
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion
public import ReasLib.CategoryTheory.Monoidal.Grp.Factorization
public import ReasLib.Topology.IrreducibleComponents.Equiv

/-!
# The identity irreducible component as a subgroup

This file constructs the group operations on the identity irreducible component of a group
scheme over an algebraically closed field and records compactness and translation properties.
-/

@[expose] public section

open CategoryTheory
open MonoidalCategory MonObj CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry.GroupScheme

/-- Over an algebraically closed field, the unit, multiplication, and inverse of a group scheme
factor through its identity irreducible component. -/
lemma identityComponentFactorization_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : SchemeOverField K) [GrpObj G] :
    let I : irreducibleComponents G.left := identityIrreducibleComponent G
    let IOver : SchemeOverField K := Over.mk (G.left.irreducibleComponentSubschemeι I ≫ G.hom)
    let j : IOver ⟶ G := Over.homMk (G.left.irreducibleComponentSubschemeι I)
    Nonempty (GrpObj.Factorization j) := by
  classical
  let I : irreducibleComponents G.left := identityIrreducibleComponent G
  let IOver : SchemeOverField K := Over.mk (G.left.irreducibleComponentSubschemeι I ≫ G.hom)
  let j : IOver ⟶ G := Over.homMk (G.left.irreducibleComponentSubschemeι I)
  -- Local instance justification (proof-local temporary data): the component inclusion is used as a closed immersion only to construct the three operation lifts.
  let _ : IsClosedImmersion j.left := by
    change IsClosedImmersion (G.left.irreducibleComponentSubschemeι I)
    infer_instance
  have hRangej : Set.range j.left = (I : Set G.left) := by
    have hRangeClosed :
        Set.range (G.left.irreducibleComponentSubschemeι I) =
          (G.left.irreducibleComponentClosed I : Set G.left) :=
      Scheme.IdealSheafData.range_vanishingIdeal_subschemeι
        (G.left.irreducibleComponentClosed I)
    change Set.range (G.left.irreducibleComponentSubschemeι I) =
      (G.left.irreducibleComponentClosed I : Set G.left)
    simpa [Scheme.mem_irreducibleComponentClosed] using hRangeClosed
  obtain ⟨oneLeft, honeLeft, _⟩ :=
    existsUnique_lift_identityPoint_into_componentSubscheme G I
      (identity_mem_identityIrreducibleComponent G)
  let one : 𝟙_ (SchemeOverField K) ⟶ IOver := Over.homMk oneLeft <| by
    change oneLeft ≫ G.left.irreducibleComponentSubschemeι I ≫ G.hom =
      (𝟙_ (SchemeOverField K)).hom
    calc
      oneLeft ≫ G.left.irreducibleComponentSubschemeι I ≫ G.hom =
          η[G].left ≫ G.hom := by
            simpa [Category.assoc] using congrArg (fun f ↦ f ≫ G.hom) honeLeft
      _ = (𝟙_ (SchemeOverField K)).hom := Over.w η[G]
  have hone : one ≫ j = η[G] := by
    apply Over.OverMorphism.ext
    exact honeLeft
  -- Local instance justification (proof-local temporary data): irreducibility of the component subscheme is used only to control the images of the lifted operations.
  haveI : IrreducibleSpace IOver.left := by
    change IrreducibleSpace (G.left.irreducibleComponentSubscheme I)
    infer_instance
  -- Local instance justification (proof-local temporary data): reducedness of the component subscheme is used only by closed-immersion factorization.
  let _ : IsReduced IOver.left := by
    change IsReduced (G.left.irreducibleComponentSubscheme I)
    infer_instance
  have hInvRange : Set.range (j.left ≫ ι[G].left) ⊆ Set.range j.left := by
    let m : IOver.left ⟶ G.left := j.left ≫ ι[G].left
    have hmRangeIrreducible : IsIrreducible (Set.range m) := by
      simpa [Set.image_univ] using
        (IrreducibleSpace.isIrreducible_univ IOver.left).image
          m.base m.continuous.continuousOn
    obtain ⟨W, hW, hmW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (Set.range m) hmRangeIrreducible
    let Wc : irreducibleComponents G.left := ⟨W, hW⟩
    have hIdMemRange : η[G].left (IsLocalRing.closedPoint K) ∈ Set.range m := by
      refine ⟨one.left (IsLocalRing.closedPoint K), ?_⟩
      have hcomp :
          one.left ≫ j.left ≫ ι[G].left = η[G].left := by
        have hcompOver : one ≫ j ≫ ι[G] = η[G] := by
          calc
            one ≫ j ≫ ι[G] = η[G] ≫ ι[G] := by
              simpa [Category.assoc] using congrArg (fun f ↦ f ≫ ι[G]) hone
            _ = η[G] := CategoryTheory.GrpObj.one_inv
        simpa [Category.assoc] using congrArg Over.Hom.left hcompOver
      exact congrArg (fun f : (𝟙_ (SchemeOverField K)).left ⟶ G.left ↦
        f (IsLocalRing.closedPoint K)) hcomp
    have hIdMemW : η[G].left (IsLocalRing.closedPoint K) ∈ (Wc : Set G.left) :=
      hmW hIdMemRange
    have hWI : Wc = I := eqIdentityIrreducibleComponentOfMem_isAlgClosed G hIdMemW
    intro x hx
    have hxW : x ∈ (Wc : Set G.left) := hmW hx
    rw [hWI] at hxW
    simpa [hRangej] using hxW
  obtain ⟨invLeft, hinvLeft, _⟩ :=
    (AlgebraicGeometry.IsClosedImmersion.existsUnique_lift_iff_range_subset
      j.left (j.left ≫ ι[G].left)).2 hInvRange
  let inv : IOver ⟶ IOver := Over.homMk invLeft <| by
    calc
      invLeft ≫ IOver.hom = invLeft ≫ j.left ≫ G.hom := by rfl
      _ = (j.left ≫ ι[G].left) ≫ G.hom := by
            simpa [Category.assoc] using congrArg (fun f ↦ f ≫ G.hom) hinvLeft
      _ = IOver.hom := by simpa [Category.assoc] using (Over.w (j ≫ ι[G]))
  have hmulSource :
      IrreducibleSpace (IOver ⊗ IOver).left := by
    -- Local instance justification (proof-local temporary data): geometric irreducibility of the component is used only for this product irreducibility argument.
    let _ : GeometricallyIrreducible IOver.hom := by
      change GeometricallyIrreducible (G.left.irreducibleComponentSubschemeι I ≫ G.hom)
      infer_instance
    -- Local instance justification (proof-local temporary data): universal openness is used only to provide the open pullback projection in this product argument.
    let _ : UniversallyOpen IOver.hom := by infer_instance
    change IrreducibleSpace ↥(Limits.pullback IOver.hom IOver.hom)
    exact GeometricallyIrreducible.irreducibleSpace
      (f := Limits.pullback.snd IOver.hom IOver.hom)
      (hf := (Limits.pullback.snd IOver.hom IOver.hom).isOpenMap)
  -- Local instance justification (proof-local temporary data): algebraic closedness supplies perfectness only for reducedness of this product.
  let _ : PerfectField K := by infer_instance
  -- Local instance justification (proof-local temporary data): reducedness of this product is used only by closed-immersion factorization of multiplication.
  let _ : IsReduced (IOver ⊗ IOver).left := by
    change IsReduced (Limits.pullback IOver.hom IOver.hom : Scheme)
    exact AlgebraicGeometry.SchemeOverField.isReduced_pullback_of_isReduced_of_perfectField
      IOver IOver
  have hMulRange :
      Set.range (((j ⊗ₘ j) ≫ μ[G]).left) ⊆ Set.range j.left := by
    -- Local instance justification (proof-local temporary data): the proved product irreducibility is used only to control the multiplication image.
    let _ : IrreducibleSpace (IOver ⊗ IOver).left := hmulSource
    let m : (IOver ⊗ IOver).left ⟶ G.left := ((j ⊗ₘ j) ≫ μ[G]).left
    have hmRangeIrreducible : IsIrreducible (Set.range m) := by
      simpa [Set.image_univ] using
        (IrreducibleSpace.isIrreducible_univ (IOver ⊗ IOver).left).image
          m.base m.continuous.continuousOn
    obtain ⟨W, hW, hmW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (Set.range m) hmRangeIrreducible
    let Wc : irreducibleComponents G.left := ⟨W, hW⟩
    have hIdMemRange : η[G].left (IsLocalRing.closedPoint K) ∈ Set.range m := by
      refine ⟨(lift one one).left (IsLocalRing.closedPoint K), ?_⟩
      change
        (Over.Hom.left (lift one one ≫ ((j ⊗ₘ j) ≫ μ[G])))
          (IsLocalRing.closedPoint K) =
          η[G].left (IsLocalRing.closedPoint K)
      have hSection : lift one one ≫ ((j ⊗ₘ j) ≫ μ[G]) = η[G] := by
        have hLiftMap :
            lift one one ≫ (j ⊗ₘ j) = lift (one ≫ j) (one ≫ j) := by
          simpa using lift_map one one j j
        calc
          lift one one ≫ ((j ⊗ₘ j) ≫ μ[G]) =
              (lift one one ≫ (j ⊗ₘ j)) ≫ μ[G] := by simp
          _ = lift (one ≫ j) (one ≫ j) ≫ μ[G] := by rw [hLiftMap]
          _ = lift η[G] η[G] ≫ μ[G] := by simpa [hone]
          _ = η[G] := by
                simpa using
                  (CategoryTheory.MonObj.lift_comp_one_right
                    (B := G) (f := η[G]) (g := toUnit (𝟙_ (SchemeOverField K))))
      exact congrArg
          (fun f : (𝟙_ (SchemeOverField K)).left ⟶ G.left ↦
            f (IsLocalRing.closedPoint K))
          (congrArg Over.Hom.left hSection)
    have hIdMemW : η[G].left (IsLocalRing.closedPoint K) ∈ (Wc : Set G.left) :=
      hmW hIdMemRange
    have hWI : Wc = I := eqIdentityIrreducibleComponentOfMem_isAlgClosed G hIdMemW
    intro x hx
    have hxW : x ∈ (Wc : Set G.left) := hmW hx
    rw [hWI] at hxW
    simpa [hRangej] using hxW
  obtain ⟨mulLeft, hmulLeft, _⟩ :=
    (AlgebraicGeometry.IsClosedImmersion.existsUnique_lift_iff_range_subset
      j.left (((j ⊗ₘ j) ≫ μ[G]).left)).2 hMulRange
  let mul : IOver ⊗ IOver ⟶ IOver := Over.homMk mulLeft <| by
    calc
      mulLeft ≫ IOver.hom = mulLeft ≫ j.left ≫ G.hom := by rfl
      _ = (((j ⊗ₘ j) ≫ μ[G]).left) ≫ G.hom := by
            simpa [Category.assoc] using congrArg (fun f ↦ f ≫ G.hom) hmulLeft
      _ = (IOver ⊗ IOver).hom := by simpa [Category.assoc] using (Over.w ((j ⊗ₘ j) ≫ μ[G]))
  refine ⟨{ one := one, mul := mul, inv := inv, one_hom := ?_, mul_hom := ?_, inv_hom := ?_ }⟩
  · exact hone
  · apply Over.OverMorphism.ext
    exact hmulLeft
  · apply Over.OverMorphism.ext
    exact hinvLeft

/-- Over an algebraically closed field, the identity irreducible component is compact as a subset
of the ambient group scheme. -/
lemma identityComponentIsCompact_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : SchemeOverField K) [GrpObj G] :
    let I : irreducibleComponents G.left := identityIrreducibleComponent G
    IsCompact (I : Set G.left) := by
  classical
  let I : irreducibleComponents G.left := identityIrreducibleComponent G
  let IOver : SchemeOverField K := Over.mk (G.left.irreducibleComponentSubschemeι I ≫ G.hom)
  let j : IOver ⟶ G := Over.homMk (G.left.irreducibleComponentSubschemeι I)
  -- Local instance justification (proof-local temporary data): the component inclusion is used as a closed immersion only to derive monicity and identify its range.
  let _ : IsClosedImmersion j.left := by
    change IsClosedImmersion (G.left.irreducibleComponentSubschemeι I)
    infer_instance
  -- Local instance justification (proof-local temporary data): monicity of this component inclusion is needed only to turn its factorization into a group structure.
  let _ : Mono j := CategoryTheory.Over.mono_of_mono_left j
  change IsCompact (I : Set G.left)
  obtain ⟨F⟩ := identityComponentFactorization_isAlgClosed G
  -- Local instance justification (noncanonical choice): this chosen factorization supplies the group structure only for the component compactness argument.
  let _ : GrpObj IOver := F.toGrpObj
  -- Local instance justification (proof-local temporary data): irreducibility of the component subscheme is used only to invoke compactness of irreducible group schemes.
  haveI : IrreducibleSpace IOver.left := by
    change IrreducibleSpace (G.left.irreducibleComponentSubscheme I)
    infer_instance
  -- Local instance justification (proof-local temporary data): compactness is consumed only to map the component's universal compact set into the ambient scheme.
  haveI : CompactSpace IOver.left := by
    infer_instance
  have hRangej : Set.range j.left = (I : Set G.left) := by
    have hRangeClosed :
        Set.range (G.left.irreducibleComponentSubschemeι I) =
          (G.left.irreducibleComponentClosed I : Set G.left) :=
      Scheme.IdealSheafData.range_vanishingIdeal_subschemeι
        (G.left.irreducibleComponentClosed I)
    change Set.range (G.left.irreducibleComponentSubschemeι I) =
      (G.left.irreducibleComponentClosed I : Set G.left)
    simpa [Scheme.mem_irreducibleComponentClosed] using hRangeClosed
  rw [← hRangej]
  simpa [Set.image_univ] using CompactSpace.isCompact_univ.image j.left.continuous

/-- The irreducible component through a rational point is the right translate of the identity
component by that point. -/
lemma eq_translate_identityIrreducibleComponent_of_mem
    {K : Type u} [Field K] [IsAlgClosed K]
    (G : SchemeOverField K) [GrpObj G]
    (g : 𝟙_ (SchemeOverField K) ⟶ G)
    {Z : irreducibleComponents G.left}
    (hZ : g.left (IsLocalRing.closedPoint K) ∈ (Z : Set G.left)) :
    Z =
      let e : G.left ≃ₜ G.left :=
        Scheme.homeoOfIso (asIso ((CategoryTheory.GrpObj.mulRight g).hom.left))
      e.irreducibleComponentsEquiv (identityIrreducibleComponent G) := by
  classical
  let e : G.left ≃ₜ G.left :=
    Scheme.homeoOfIso (asIso ((CategoryTheory.GrpObj.mulRight g).hom.left))
  have hgId :
      e (η[G].left (IsLocalRing.closedPoint K)) =
        g.left (IsLocalRing.closedPoint K) := by
    change ((CategoryTheory.GrpObj.mulRight g).hom.left
      (η[G].left (IsLocalRing.closedPoint K))) =
        g.left (IsLocalRing.closedPoint K)
    have hmul :
        η[G] ≫ (CategoryTheory.GrpObj.mulRight g).hom = g := by
      calc
        η[G] ≫ (CategoryTheory.GrpObj.mulRight g).hom = lift η[G] g ≫ μ[G] := by
          simp [CategoryTheory.GrpObj.mulRight, comp_lift_assoc]
        _ = g := by
          simpa using
            (CategoryTheory.MonObj.lift_comp_one_left
              (B := G) (f := toUnit (𝟙_ (SchemeOverField K))) (g := g))
    exact congrArg
      (fun f : (𝟙_ (SchemeOverField K)).left ⟶ G.left ↦
        f (IsLocalRing.closedPoint K))
      (congrArg Over.Hom.left hmul)
  have hIdMem :
      η[G].left (IsLocalRing.closedPoint K) ∈
        ((((e.irreducibleComponentsEquiv).symm) Z : irreducibleComponents G.left) : Set G.left) := by
    rw [Homeomorph.coe_irreducibleComponentsEquiv_symm_apply]
    change e (η[G].left (IsLocalRing.closedPoint K)) ∈ (Z : Set G.left)
    exact hgId.symm ▸ hZ
  have hEq :
      ((e.irreducibleComponentsEquiv).symm) Z = identityIrreducibleComponent G :=
    eqIdentityIrreducibleComponentOfMem_isAlgClosed G hIdMem
  simpa [e] using congrArg e.irreducibleComponentsEquiv hEq

end AlgebraicGeometry.GroupScheme
