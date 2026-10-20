/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Cartesian
public import ReasLib.AlgebraicGeometry.ChowGroup.FieldFundamental
public import ReasLib.AlgebraicGeometry.BivariantClass.Additive
public import ReasLib.AlgebraicGeometry.ChowGroup.ExteriorProduct
public import ReasLib.AlgebraicGeometry.ChowGroup.Reindex

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

namespace BivariantClass

/-- The cap family determined by a Chow class: take exterior product and transport from
`X ⨯ Y'` to the displayed cartesian representative. -/
noncomputable def ofChowCap (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    CapFamily (fun _ ↦ 0) (terminal.from X) p :=
  fun {X' Y'} _ _ i f' g _ square n ↦
    (ChowGroup.map (fun _ ↦ 0) (X ⨯ Y') X'
      (SchemeOverField.productIsoOfIsPullback X i f' g square).inv (n - p)).comp
      ((@ChowGroup.reindex (X ⨯ Y').left
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ (X ⨯ Y').hom inferInstance
            (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
              (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
          ((X ⨯ Y').hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance
          _ _ (neg_add_eq_sub p n)).toAddMonoidHom.comp
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
        (@ChowGroup.reindex (X ⨯ Y').left
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ (X ⨯ Y').hom inferInstance
            (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
              (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
          ((X ⨯ Y').hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance
          _ _ (neg_add_eq_sub p n)
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
    ofChowClass X p 0 = pointwiseZero (fun _ ↦ 0) (terminal.from X) p := sorry

/-- The bivariant class construction preserves addition of Chow classes. -/
theorem ofChowClass_add (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha beta : RelativeChow (fun _ ↦ 0) X (-p)) :
    ofChowClass X p (alpha + beta) =
      pointwiseAdd (fun _ ↦ 0) (terminal.from X) p
        (ofChowClass X p alpha) (ofChowClass X p beta) := sorry

/-- Exterior product defines an additive map from Chow classes to bivariant classes. -/
noncomputable def ofChow (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) :
    @AddMonoidHom (RelativeChow (fun _ ↦ 0) X (-p))
      (BivariantClass (fun _ ↦ 0) (terminal.from X) p) inferInstance
      (@AddZeroClass.toAddZero _
        (pointwiseAddCommGroup (fun _ ↦ 0) (terminal.from X) p).toAddCommMonoid.toAddMonoid.toAddZeroClass) :=
  let targetAddZero := @AddZeroClass.toAddZero _
    (pointwiseAddCommGroup (fun _ ↦ 0) (terminal.from X) p).toAddCommMonoid.toAddMonoid.toAddZeroClass
  @AddMonoidHom.mk _ _ inferInstance targetAddZero
    (@ZeroHom.mk _ _ inferInstance targetAddZero.toZero
      (ofChowClass X p) (ofChowClass_zero X p)) (ofChowClass_add X p)

/-- The additive map `ofChow` sends `alpha` to its exterior-product bivariant class. -/
theorem ofChow_apply (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    ofChow X p alpha = ofChowClass X p alpha := sorry

/-- Evaluation of a bivariant class on the fundamental class of `Spec k`. -/
noncomputable def toChowValue (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    RelativeChow (fun _ ↦ 0) X (-p) :=
  @ChowGroup.reindex X.left
    (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
      (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
        (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
    (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance _ _ (zero_sub p)
    (c.cap (𝟙 X) (terminal.from X) (𝟙 (⊤_ (SchemeOverField k)))
      IsPullback.of_id_fst 0 (ChowGroup.specFundamentalClass k))

/-- The value `toChowValue c` is the formal cap product `c ∩ [Spec k]`. -/
theorem toChowValue_def (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    toChowValue X p c =
      @ChowGroup.reindex X.left
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ X.hom inferInstance
          (@instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
            (CommRingCat.of k) PrincipalIdealRing.isNoetherianRing))
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance _ _ (zero_sub p)
        (c.cap (𝟙 X) (terminal.from X) (𝟙 (⊤_ (SchemeOverField k)))
          IsPullback.of_id_fst 0 (ChowGroup.specFundamentalClass k)) := sorry

/-- Evaluation on `[Spec k]` sends the zero bivariant class to zero. -/
theorem toChowValue_zero (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) :
    toChowValue X p (pointwiseZero (fun _ ↦ 0) (terminal.from X) p) = 0 := sorry

/-- Evaluation on `[Spec k]` preserves addition of bivariant classes. -/
theorem toChowValue_add (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c d : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    toChowValue X p (pointwiseAdd (fun _ ↦ 0) (terminal.from X) p c d) =
      toChowValue X p c + toChowValue X p d := sorry

/-- Capping with `[Spec k]` as an additive map from bivariant classes to Chow classes. -/
noncomputable def toChow (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) :
    @AddMonoidHom (BivariantClass (fun _ ↦ 0) (terminal.from X) p)
      (RelativeChow (fun _ ↦ 0) X (-p))
      (@AddZeroClass.toAddZero _
        (pointwiseAddCommGroup (fun _ ↦ 0) (terminal.from X) p).toAddCommMonoid.toAddMonoid.toAddZeroClass)
      inferInstance :=
  let sourceAddZero := @AddZeroClass.toAddZero _
    (pointwiseAddCommGroup (fun _ ↦ 0) (terminal.from X) p).toAddCommMonoid.toAddMonoid.toAddZeroClass
  @AddMonoidHom.mk _ _ sourceAddZero inferInstance
    (@ZeroHom.mk _ _ sourceAddZero.toZero inferInstance
      (toChowValue X p) (toChowValue_zero X p)) (toChowValue_add X p)

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
    (p : ℤ) :
    @AddEquiv (BivariantClass (fun _ ↦ 0) (terminal.from X) p)
      (RelativeChow (fun _ ↦ 0) X (-p))
      (@AddSemigroup.toAdd _
        (pointwiseAddCommGroup (fun _ ↦ 0) (terminal.from X) p).toAddCommMonoid.toAddMonoid.toAddSemigroup)
      inferInstance :=
  let sourceAdd := @AddSemigroup.toAdd _
    (pointwiseAddCommGroup (fun _ ↦ 0) (terminal.from X) p).toAddCommMonoid.toAddMonoid.toAddSemigroup
  @AddEquiv.mk _ _ sourceAdd inferInstance
    { toFun := toChow X p
      invFun := ofChow X p
      left_inv := ofChow_toChow X p
      right_inv := toChow_ofChow X p }
    (toChowValue_add X p)

/-- The forward map of `chowEquiv` is capping with `[Spec k]`. -/
theorem chowEquiv_apply (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p) :
    chowEquiv X p c = toChow X p c := sorry

/-- The inverse map of `chowEquiv` sends a Chow class to its exterior-product class. -/
theorem chowEquiv_symm_apply (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) X (-p)) :
    EquivLike.inv (chowEquiv X p) alpha = ofChow X p alpha := sorry

end BivariantClass

end AlgebraicGeometry
