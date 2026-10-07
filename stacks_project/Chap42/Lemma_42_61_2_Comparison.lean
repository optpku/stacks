module

public import stacks_project.Chap42.Lemma_42_61_1_ExteriorProduct
public import stacks_project.Chap42.Remark_42_35_5_Composition
public import stacks_project.Chap42.«42_37_1_1_FundamentalCycle»

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

namespace SchemeOverField

/-- The structure morphism of the chosen terminal scheme over a field is locally of
finite type. -/
instance instTerminalLocallyOfFiniteType :
    LocallyOfFiniteType (⊤_ (SchemeOverField k)).hom := sorry

/-- The product projections over a field form a pullback square against the maps to the
terminal scheme over that field. -/
theorem productIsPullback (X : SchemeOverField k) {Y : SchemeOverField k}
    (g : Y ⟶ ⊤_ (SchemeOverField k)) :
    IsPullback ((Limits.prod.fst : X ⨯ Y ⟶ X).left)
      ((Limits.prod.snd : X ⨯ Y ⟶ Y).left) (terminal.from X).left g.left := sorry

/-- The canonical pullback comparison with `X ⨯ Y` respects the structure maps to
`Spec k`. -/
theorem productIsoOfIsPullback_hom_base
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ ⊤_ (SchemeOverField k))
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    (square.isoIsPullback X.left Y.left (productIsPullback X g)).hom ≫
        (X ⨯ Y).hom = X'.hom := sorry

/-- The canonical isomorphism from an arbitrary cartesian representative over `Spec k`
to the product representative. -/
noncomputable def productIsoOfIsPullback
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ ⊤_ (SchemeOverField k))
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    X' ≅ X ⨯ Y :=
  Over.isoMk (square.isoIsPullback X.left Y.left (productIsPullback X g))
    (productIsoOfIsPullback_hom_base X i f' g square)

/-- The product comparison followed by the first projection is the given map to `X`. -/
theorem productIsoOfIsPullback_hom_fst
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ ⊤_ (SchemeOverField k))
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    (productIsoOfIsPullback X i f' g square).hom ≫ Limits.prod.fst = i := sorry

/-- The product comparison followed by the second projection is the given map to `Y`. -/
theorem productIsoOfIsPullback_hom_snd
    (X : SchemeOverField k) {X' Y : SchemeOverField k}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ ⊤_ (SchemeOverField k))
    (square : IsPullback i.left f'.left (terminal.from X).left g.left) :
    (productIsoOfIsPullback X i f' g square).hom ≫ Limits.prod.snd = f' := sorry

end SchemeOverField

namespace ChowGroup

/-- The degree-zero fundamental Chow class of the spectrum of a field. -/
noncomputable def specFundamentalClass (k : Type u) [Field k] :
    RelativeChow (fun _ ↦ 0) (⊤_ (SchemeOverField k)) 0 :=
  @chowClass (⊤_ (SchemeOverField k)).left
    (LocallyOfFiniteType.isLocallyNoetherian (⊤_ (SchemeOverField k)).hom)
    ((⊤_ (SchemeOverField k)).hom.relativeDimensionFunction (fun _ ↦ 0))
    inferInstance 0
    (@CycleGroup.fundamental (⊤_ (SchemeOverField k)).left
      (LocallyOfFiniteType.isLocallyNoetherian (⊤_ (SchemeOverField k)).hom)
      ((⊤_ (SchemeOverField k)).hom.relativeDimensionFunction (fun _ ↦ 0)) 0)

/-- The fundamental class of `Spec k` is represented by its fundamental cycle. -/
theorem specFundamentalClass_def (k : Type u) [Field k] :
    specFundamentalClass k =
      @chowClass (⊤_ (SchemeOverField k)).left
        (LocallyOfFiniteType.isLocallyNoetherian (⊤_ (SchemeOverField k)).hom)
        ((⊤_ (SchemeOverField k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        inferInstance 0
        (@CycleGroup.fundamental (⊤_ (SchemeOverField k)).left
          (LocallyOfFiniteType.isLocallyNoetherian (⊤_ (SchemeOverField k)).hom)
          ((⊤_ (SchemeOverField k)).hom.relativeDimensionFunction (fun _ ↦ 0)) 0) := sorry

end ChowGroup

namespace BivariantClass

/-- The cap family determined by a Chow class: take exterior product and transport from
`X ⨯ Y'` to the displayed cartesian representative. -/
noncomputable def ofChowCap (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    CapFamily (fun _ ↦ 0) (terminal.from X) p :=
  fun {X' Y'} _ _ i f' g _ square n ↦
    (ChowGroup.map (fun _ ↦ 0) (X ⨯ Y') X'
      (SchemeOverField.productIsoOfIsPullback X i f' g square).inv (n - p)).comp
      ((castRelativeDegree (fun _ ↦ 0) (neg_add_eq_sub p n)).comp
        (ChowGroup.exteriorProductPairing X Y' (-p) n alpha))

/-- Evaluation of the cap family attached to `alpha` is exterior product followed by
degree transport and pushforward along the inverse product comparison. -/
theorem ofChowCap_apply (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p))
    {X' Y' : SchemeOverField k} [LocallyOfFiniteType X'.hom]
    [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ ⊤_ (SchemeOverField k))
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (terminal.from X).left g.left)
    (n : ℤ) (beta : RelativeChow (fun _ ↦ 0) Y' n) :
    ofChowCap X p alpha i f' g square n beta =
      ChowGroup.map (fun _ ↦ 0) (X ⨯ Y') X'
        (SchemeOverField.productIsoOfIsPullback X i f' g square).inv (n - p)
        (castRelativeDegree (fun _ ↦ 0) (neg_add_eq_sub p n)
          (ChowGroup.exteriorProductPairing X Y' (-p) n alpha beta)) := sorry

/-- Exterior-product cap families commute with proper pushforward. -/
theorem ofChowCap_mapProper (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    CompatibleWithProperPushforward (fun _ ↦ 0) (ofChowCap X p alpha) := sorry

/-- Exterior-product cap families commute with flat pullback. -/
theorem ofChowCap_pullbackFlat (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    CompatibleWithFlatPullback (fun _ ↦ 0) (ofChowCap X p alpha) := sorry

/-- Exterior-product cap families commute with effective-Cartier Gysin pullback. -/
theorem ofChowCap_gysinCartier (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    CompatibleWithCartierGysin (fun _ ↦ 0) (ofChowCap X p alpha) := sorry

/-- The bivariant class whose action is exterior product with `alpha`. -/
noncomputable def ofChowClass (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    BivariantClass (fun _ ↦ 0) (terminal.from X) p where
  cap := ofChowCap X p alpha
  map_proper := ofChowCap_mapProper X p alpha
  pullback_flat := ofChowCap_pullbackFlat X p alpha
  gysin_cartier := ofChowCap_gysinCartier X p alpha

/-- The cap field of `ofChowClass` is the exterior-product cap family. -/
theorem ofChowClass_cap (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p))
    {X' Y' : SchemeOverField k} [LocallyOfFiniteType X'.hom]
    [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ ⊤_ (SchemeOverField k))
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (terminal.from X).left g.left)
    (n : ℤ) (beta : RelativeChow (fun _ ↦ 0) Y' n) :
    (ofChowClass X p alpha).cap i f' g square n beta =
      ofChowCap X p alpha i f' g square n beta := sorry

/-- The bivariant class associated to the zero Chow class is zero. -/
theorem ofChowClass_zero (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) :
    ofChowClass X p 0 = 0 := sorry

/-- The bivariant class construction preserves addition of Chow classes. -/
theorem ofChowClass_add (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha beta : RelativeChow (fun _ ↦ 0) X (-p)) :
    ofChowClass X p (alpha + beta) = ofChowClass X p alpha + ofChowClass X p beta := sorry

/-- Exterior product defines an additive map from Chow classes to bivariant classes. -/
noncomputable def ofChow (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) : RelativeChow (fun _ ↦ 0) X (-p) →+
      BivariantClass (fun _ ↦ 0) (terminal.from X) p where
  toFun := ofChowClass X p
  map_zero' := ofChowClass_zero X p
  map_add' := ofChowClass_add X p

/-- The additive map `ofChow` sends `alpha` to its exterior-product bivariant class. -/
theorem ofChow_apply (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    ofChow X p alpha = ofChowClass X p alpha := sorry

/-- Evaluation of a bivariant class on the fundamental class of `Spec k`. -/
noncomputable def toChowValue (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    RelativeChow (fun _ ↦ 0) X (-p) :=
  castRelativeDegree (fun _ ↦ 0) (zero_sub p)
    (c.cap (𝟙 X) (terminal.from X) (𝟙 (⊤_ (SchemeOverField k)))
      IsPullback.of_id_fst 0 (ChowGroup.specFundamentalClass k))

/-- The value `toChowValue c` is the formal cap product `c ∩ [Spec k]`. -/
theorem toChowValue_def (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    toChowValue X p c =
      castRelativeDegree (fun _ ↦ 0) (zero_sub p)
        (c.cap (𝟙 X) (terminal.from X) (𝟙 (⊤_ (SchemeOverField k)))
          IsPullback.of_id_fst 0 (ChowGroup.specFundamentalClass k)) := sorry

/-- Evaluation on `[Spec k]` sends the zero bivariant class to zero. -/
theorem toChowValue_zero (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) :
    toChowValue X p 0 = 0 := sorry

/-- Evaluation on `[Spec k]` preserves addition of bivariant classes. -/
theorem toChowValue_add (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c d : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    toChowValue X p (c + d) = toChowValue X p c + toChowValue X p d := sorry

/-- Capping with `[Spec k]` as an additive map from bivariant classes to Chow classes. -/
noncomputable def toChow (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) : BivariantClass (fun _ ↦ 0) (terminal.from X) p →+
      RelativeChow (fun _ ↦ 0) X (-p) where
  toFun := toChowValue X p
  map_zero' := toChowValue_zero X p
  map_add' := toChowValue_add X p

/-- The additive map `toChow` is evaluation on the fundamental class of `Spec k`. -/
theorem toChow_apply (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    toChow X p c = toChowValue X p c := sorry

/-- Evaluation on `[Spec k]` recovers the Chow class used to define an exterior-product
bivariant class. -/
theorem toChow_ofChow (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    toChow X p (ofChow X p alpha) = alpha := sorry

/-- A bivariant class over `Spec k` is recovered from its value on `[Spec k]`. -/
theorem ofChow_toChow (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    ofChow X p (toChow X p c) = c := sorry

/-- The canonical additive identification of degree-`p` bivariant classes over a field
with degree-`-p` Chow classes. -/
noncomputable def chowEquiv (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) : BivariantClass (fun _ ↦ 0) (terminal.from X) p ≃+
      RelativeChow (fun _ ↦ 0) X (-p) where
  toFun := toChow X p
  invFun := ofChow X p
  left_inv := ofChow_toChow X p
  right_inv := toChow_ofChow X p
  map_add' := (toChow X p).map_add

/-- The forward map of `chowEquiv` is capping with `[Spec k]`. -/
theorem chowEquiv_apply (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    chowEquiv X p c = toChow X p c := sorry

/-- The inverse map of `chowEquiv` sends a Chow class to its exterior-product class. -/
theorem chowEquiv_symm_apply (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    (chowEquiv X p).symm alpha = ofChow X p alpha := sorry

end BivariantClass

end AlgebraicGeometry
