module
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger
public import ReasLib.CategoryTheory.Fibered.Lifts.Pushforward

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.LocalRing.Pullback
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal

/-!
# Self fibre products in `ArtinianLocalAlgCat`

The fibre product `A' ×_A A'` of a morphism `f : A' ⟶ A` with itself is the algebra
pullback of `f.hom` along itself, bundled as an object of `C_Λ`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable {A A' : ArtinianLocalAlgCat Λ k}

/-- The algebra pullback underlying the self fibre product. -/
abbrev selfPullbackSubalgebra (f : A' ⟶ A) :
    @Subalgebra Λ (A'.carrier × A'.carrier) _ _
      (@Prod.algebra Λ A'.carrier A'.carrier _ _ A'.algebra _ A'.algebra) :=
  @AlgHom.pullback Λ A'.carrier A'.carrier A.carrier
    _ _ A'.algebra _ A'.algebra _ A.algebra f.hom f.hom

/-- The fibre product `A' ×_A A'` is a local ring. -/
instance instIsLocalRing_selfPullback (f : A' ⟶ A) :
    IsLocalRing (@AlgHom.pullback Λ A'.carrier A'.carrier A.carrier
      _ _ A'.algebra _ A'.algebra _ A.algebra f.hom f.hom) :=
  sorry

/-- The residue-field algebra structure on the self fibre product. -/
abbrev selfPullbackResidueFieldAlgebra (f : A' ⟶ A) :
    Algebra Λ (ResidueField (selfPullbackSubalgebra f)) :=
  @ResidueField.algebra (selfPullbackSubalgebra f)
    _ (instIsLocalRing_selfPullback f) Λ inferInstance
    (@Subalgebra.algebra Λ (A'.carrier × A'.carrier) _ _
      (@Prod.algebra Λ A'.carrier A'.carrier _ _ A'.algebra _ A'.algebra)
      (selfPullbackSubalgebra f))

/-- The fibre product `A' ×_A A'` is Artinian. -/
instance instIsArtinianRing_selfPullback (f : A' ⟶ A) :
    IsArtinianRing (@AlgHom.pullback Λ A'.carrier A'.carrier A.carrier
      _ _ A'.algebra _ A'.algebra _ A.algebra f.hom f.hom) := sorry

/-- The first algebra projection of `A' ×_A A'` is local. -/
instance instIsLocalHom_selfPullbackFst (f : A' ⟶ A) :
    IsLocalHom (@AlgHom.pullbackFst Λ A'.carrier A'.carrier A.carrier
      _ _ A'.algebra _ A'.algebra _ A.algebra f.hom f.hom) := sorry

/-- The second algebra projection of `A' ×_A A'` is local. -/
instance instIsLocalHom_selfPullbackSnd (f : A' ⟶ A) :
    IsLocalHom (@AlgHom.pullbackSnd Λ A'.carrier A'.carrier A.carrier
      _ _ A'.algebra _ A'.algebra _ A.algebra f.hom f.hom) := sorry

/-- The diagonal algebra map `A' → A' ×_A A'`, sending `a` to `(a, a)`. -/
noncomputable def selfPullbackDiagonalHom (f : A' ⟶ A) :
    @AlgHom Λ A'.carrier
      (@AlgHom.pullback Λ A'.carrier A'.carrier A.carrier
        _ _ A'.algebra _ A'.algebra _ A.algebra f.hom f.hom)
      _ _ _ A'.algebra
      (@Subalgebra.algebra Λ (A'.carrier × A'.carrier) _ _
        (@Prod.algebra Λ A'.carrier A'.carrier _ _ A'.algebra _ A'.algebra)
        (@AlgHom.pullback Λ A'.carrier A'.carrier A.carrier
          _ _ A'.algebra _ A'.algebra _ A.algebra f.hom f.hom)) :=
  @AlgHom.codRestrict Λ A'.carrier (A'.carrier × A'.carrier)
    _ _ A'.algebra _
      (@Prod.algebra Λ A'.carrier A'.carrier _ _ A'.algebra _ A'.algebra)
    (@AlgHom.prod Λ A'.carrier A'.carrier A'.carrier
      _ _ A'.algebra _ A'.algebra _ A'.algebra
      (@AlgHom.id Λ A'.carrier _ _ A'.algebra)
      (@AlgHom.id Λ A'.carrier _ _ A'.algebra))
    (@AlgHom.pullback Λ A'.carrier A'.carrier A.carrier
      _ _ A'.algebra _ A'.algebra _ A.algebra f.hom f.hom) sorry

/-- The diagonal algebra map of `A' ×_A A'` is local. -/
instance instIsLocalHom_selfPullbackDiagonalHom (f : A' ⟶ A) :
    IsLocalHom (selfPullbackDiagonalHom f) := sorry

/-- Residue-field identification of `A' ×_A A'` with `k`, via the first projection
and the residue identification of `A'`. -/
noncomputable def selfPullbackResidueFieldIso (f : A' ⟶ A) :
    @AlgEquiv Λ (ResidueField (selfPullbackSubalgebra f)) k _ _ _
      (selfPullbackResidueFieldAlgebra f) inferInstance := by
  let m₁ := @ResidueField.mapAlgHom Λ
    (selfPullbackSubalgebra f) A'.carrier
    _ _ (instIsLocalRing_selfPullback f) _ A'.isLocalRing
    (@Subalgebra.algebra Λ (A'.carrier × A'.carrier) _ _
      (@Prod.algebra Λ A'.carrier A'.carrier _ _ A'.algebra _ A'.algebra)
      (selfPullbackSubalgebra f)) A'.algebra
    (@AlgHom.pullbackFst Λ A'.carrier A'.carrier A.carrier
      _ _ A'.algebra _ A'.algebra _ A.algebra f.hom f.hom) inferInstance
  let m₂ := @ResidueField.mapAlgHom Λ A'.carrier
    (selfPullbackSubalgebra f)
    _ _ A'.isLocalRing _ (instIsLocalRing_selfPullback f)
    A'.algebra
    (@Subalgebra.algebra Λ (A'.carrier × A'.carrier) _ _
      (@Prod.algebra Λ A'.carrier A'.carrier _ _ A'.algebra _ A'.algebra)
      (selfPullbackSubalgebra f))
    (selfPullbackDiagonalHom f) (instIsLocalHom_selfPullbackDiagonalHom f)
  exact AlgEquiv.ofAlgHom
    (@AlgHom.comp Λ (ResidueField (selfPullbackSubalgebra f))
      (@ResidueField A'.carrier _ A'.isLocalRing) k
      _ _ _ _ (selfPullbackResidueFieldAlgebra f)
      (@ResidueField.algebra A'.carrier _ A'.isLocalRing Λ _ A'.algebra)
      inferInstance (ArtinianLocalAlgCat.residueIsoHom A') m₁)
    (@AlgHom.comp Λ k (@ResidueField A'.carrier _ A'.isLocalRing)
      (ResidueField (selfPullbackSubalgebra f))
      _ _ _ _ inferInstance
      (@ResidueField.algebra A'.carrier _ A'.isLocalRing Λ _ A'.algebra)
      (selfPullbackResidueFieldAlgebra f) m₂
      (@AlgEquiv.toAlgHom Λ k (@ResidueField A'.carrier _ A'.isLocalRing) _ _ _
        inferInstance (@ResidueField.algebra A'.carrier _ A'.isLocalRing Λ _ A'.algebra)
        (@AlgEquiv.symm Λ (@ResidueField A'.carrier _ A'.isLocalRing) k _ _ _
          (@ResidueField.algebra A'.carrier _ A'.isLocalRing Λ _ A'.algebra)
          inferInstance A'.residueFieldIso)))
    sorry sorry

/-- The fibre product `A' ×_A A'`, viewed as an object of `ArtinianLocalAlgCat`. -/
noncomputable def selfPullback (f : A' ⟶ A) : ArtinianLocalAlgCat Λ k :=
  of (@AlgHom.pullback Λ A'.carrier A'.carrier A.carrier
    _ _ A'.algebra _ A'.algebra _ A.algebra f.hom f.hom) (selfPullbackResidueFieldIso f)

/-- The bundled self fibre product has the algebra-pullback carrier. -/
theorem selfPullback_carrier (f : A' ⟶ A) :
    (selfPullback f).carrier =
      ((@AlgHom.pullback Λ A'.carrier A'.carrier A.carrier
        _ _ A'.algebra _ A'.algebra _ A.algebra f.hom f.hom) : Type u) := sorry

/-- The first projection `A' ×_A A' ⟶ A'`. -/
noncomputable def selfPullbackFst (f : A' ⟶ A) : selfPullback f ⟶ A' :=
  Hom.of
    (@AlgHom.pullbackFst Λ A'.carrier A'.carrier A.carrier
      _ _ A'.algebra _ A'.algebra _ A.algebra f.hom f.hom)
    sorry sorry

/-- The second projection `A' ×_A A' ⟶ A'`. -/
noncomputable def selfPullbackSnd (f : A' ⟶ A) : selfPullback f ⟶ A' :=
  Hom.of
    (@AlgHom.pullbackSnd Λ A'.carrier A'.carrier A.carrier
      _ _ A'.algebra _ A'.algebra _ A.algebra f.hom f.hom)
    sorry sorry

/-- The composite `A' ×_A A' ⟶ A` of either projection with `f`. -/
noncomputable def selfPullbackToBase (f : A' ⟶ A) : selfPullback f ⟶ A :=
  selfPullbackFst f ≫ f

/-- The diagonal section `A' ⟶ A' ×_A A'` of the two projections. -/
noncomputable def selfPullbackDiagonal (f : A' ⟶ A) : A' ⟶ selfPullback f :=
  Hom.of (selfPullbackDiagonalHom f) sorry sorry

/-- The induced map into `A' ×_A A'` from a pair of maps to `A'` that agree after `f`. -/
noncomputable def selfPullbackLift {B : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (g₁ g₂ : B ⟶ A') (h : g₁ ≫ f = g₂ ≫ f) : B ⟶ selfPullback f :=
  Hom.of
    (@AlgHom.codRestrict Λ B.carrier (A'.carrier × A'.carrier)
      _ _ B.algebra _
        (@Prod.algebra Λ A'.carrier A'.carrier _ _ A'.algebra _ A'.algebra)
      (@AlgHom.prod Λ B.carrier A'.carrier A'.carrier
        _ _ B.algebra _ A'.algebra _ A'.algebra g₁.hom g₂.hom)
      (@AlgHom.pullback Λ A'.carrier A'.carrier A.carrier
        _ _ A'.algebra _ A'.algebra _ A.algebra f.hom f.hom) sorry)
    sorry sorry

/-- The underlying algebra map of `selfPullbackFst` is the first algebra projection. -/
theorem selfPullbackFst_hom (f : A' ⟶ A) :
    (selfPullbackFst f).hom =
      @AlgHom.pullbackFst Λ A'.carrier A'.carrier A.carrier
        _ _ A'.algebra _ A'.algebra _ A.algebra f.hom f.hom := sorry

/-- The underlying algebra map of `selfPullbackSnd` is the second algebra projection. -/
theorem selfPullbackSnd_hom (f : A' ⟶ A) :
    (selfPullbackSnd f).hom =
      @AlgHom.pullbackSnd Λ A'.carrier A'.carrier A.carrier
        _ _ A'.algebra _ A'.algebra _ A.algebra f.hom f.hom := sorry

/-- The map to the base is the first projection followed by `f`. -/
theorem selfPullbackToBase_eq (f : A' ⟶ A) :
    selfPullbackToBase f = selfPullbackFst f ≫ f := sorry

/-- The two projections of `A' ×_A A'` agree after composing with `f`. -/
theorem selfPullbackFst_comp_eq_snd_comp (f : A' ⟶ A) :
    selfPullbackFst f ≫ f = selfPullbackSnd f ≫ f := sorry

/-- The second projection followed by `f` is the map from the self fibre product to the base. -/
theorem selfPullbackSnd_comp_eq_toBase (f : A' ⟶ A) :
    selfPullbackSnd f ≫ f = selfPullbackToBase f := sorry

/-- The diagonal is a section of the first projection. -/
theorem selfPullbackDiagonal_comp_fst (f : A' ⟶ A) :
    selfPullbackDiagonal f ≫ selfPullbackFst f = 𝟙 A' := sorry

/-- The diagonal is a section of the second projection. -/
theorem selfPullbackDiagonal_comp_snd (f : A' ⟶ A) :
    selfPullbackDiagonal f ≫ selfPullbackSnd f = 𝟙 A' := sorry

/-- The induced lift projects to the first given map. -/
theorem selfPullbackLift_comp_fst {B : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (g₁ g₂ : B ⟶ A') (h : g₁ ≫ f = g₂ ≫ f) :
    selfPullbackLift f g₁ g₂ h ≫ selfPullbackFst f = g₁ := sorry

/-- The induced lift projects to the second given map. -/
theorem selfPullbackLift_comp_snd {B : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (g₁ g₂ : B ⟶ A') (h : g₁ ≫ f = g₂ ≫ f) :
    selfPullbackLift f g₁ g₂ h ≫ selfPullbackSnd f = g₂ := sorry

/-- The self-cospan square is a pullback in `ArtinianLocalAlgCat`. -/
theorem isPullback_selfPullback (f : A' ⟶ A) :
    IsPullback (selfPullbackFst f) (selfPullbackSnd f) f f := sorry

/-- The self fibre product is a pullback cone for `f, f`, and its map to the base is
the composite of the first projection with `f`. -/
theorem selfPullback_spec (f : A' ⟶ A) :
    IsPullback (selfPullbackFst f) (selfPullbackSnd f) f f ∧
      selfPullbackToBase f = selfPullbackFst f ≫ f := sorry

end ArtinianLocalAlgCat
open CategoryTheory
open Functor Fiber ArtinianLocalAlgCat

universe v w

variable {F : Type v} [Category.{w} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

variable {A A' : ArtinianLocalAlgCat Λ k}

/-- The Rim-Schlessinger condition includes cofiberedness in groupoids. -/
instance instIsFiberedInGroupoids_ofHasRimSchlessinger [HasRimSchlessinger p] :
    IsFibered.InGroupoids p.op :=
  HasRimSchlessinger.isCofiberedInGroupoids
/-- The inverse comparison sending a lift to `A' ×_A A'` to the pair of its
pushforwards along the two projections. -/
noncomputable def liftsSelfPullbackToProd [IsFibered.InGroupoids p.op]
    (f : A' ⟶ A) (x : p.Fiber A) :
    lifts p (selfPullbackToBase f) x → lifts p f x × lifts p f x :=
  Quotient.lift
    (fun a ↦
      (Quotient.mk'' (ObjectLift.pushforwardAlong (selfPullbackFst f) f a),
        Quotient.mk''
          (ObjectLift.pushforwardAlong (selfPullbackSnd f) f
            (ObjectLift.congr (selfPullbackSnd_comp_eq_toBase f).symm a))))
    sorry

/-- On a represented class, `liftsSelfPullbackToProd` is the pair of projection
pushforwards. -/
theorem liftsSelfPullbackToProd_mk [IsFibered.InGroupoids p.op]
    (f : A' ⟶ A) (x : p.Fiber A) (a : ObjectLift p (selfPullbackToBase f) x) :
    liftsSelfPullbackToProd f x (Quotient.mk'' a) =
      (Quotient.mk'' (ObjectLift.pushforwardAlong (selfPullbackFst f) f a),
        Quotient.mk''
          (ObjectLift.pushforwardAlong (selfPullbackSnd f) f
            (ObjectLift.congr (selfPullbackSnd_comp_eq_toBase f).symm a))) :=
  sorry

/-- A lift along a surjection in `ArtinianLocalAlgCat` has surjective image under `p`. -/
theorem ObjectLift.map_hom_surjective {f : A' ⟶ A} (hf : Function.Surjective f.hom)
    {x : p.Fiber A} (a : ObjectLift p f x) :
    Function.Surjective (p.map a.hom).hom := sorry

/-- The Rim-Schlessinger pairing of two lifts of `x` along `f` to a lift along
`A' ×_A A' ⟶ A`. -/
noncomputable def liftsSelfPullbackPair [HasRimSchlessinger p]
    {f : A' ⟶ A} (hf : Function.Surjective f.hom) {x : p.Fiber A}
    (a b : ObjectLift p f x) : ObjectLift p (selfPullbackToBase f) x :=
  let h := (inferInstance : HasRimSchlessinger p).exists_pullback a.hom b.hom
    (ObjectLift.map_hom_surjective hf b)
  let w := Classical.choose h
  let π1 := Classical.choose (Classical.choose_spec h)
  let π2 := Classical.choose (Classical.choose_spec (Classical.choose_spec h))
  let g1 : p.obj w ⟶ A' := p.map π1 ≫ eqToHom (IsHomLift.domain_eq p f a.hom)
  let g2 : p.obj w ⟶ A' := p.map π2 ≫ eqToHom (IsHomLift.domain_eq p f b.hom)
  ObjectLift.pushforwardAlong (selfPullbackLift f g1 g2 sorry) (selfPullbackToBase f)
    ⟨Over.mk (π1 ≫ a.hom), sorry⟩

/-- The two projection classes of the Rim-Schlessinger pairing are the original
classes of the paired lifts. -/
theorem liftsSelfPullbackPair_spec [HasRimSchlessinger p]
    {f : A' ⟶ A} (hf : Function.Surjective f.hom) {x : p.Fiber A}
    (a b : ObjectLift p f x) :
    (liftsSelfPullbackToProd f x (Quotient.mk'' (liftsSelfPullbackPair hf a b))).1 =
        Quotient.mk'' a ∧
      (liftsSelfPullbackToProd f x (Quotient.mk'' (liftsSelfPullbackPair hf a b))).2 =
        Quotient.mk'' b := sorry

/-- The forward comparison sending a pair of lifts of `x` along `f` to a lift along
`A' ×_A A' ⟶ A`. -/
noncomputable def liftsSelfPullbackFromProd [HasRimSchlessinger p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom) (x : p.Fiber A) :
    lifts p f x × lifts p f x → lifts p (selfPullbackToBase f) x :=
  fun ab ↦
    Quotient.liftOn₂ ab.1 ab.2
      (fun a b ↦ Quotient.mk'' (liftsSelfPullbackPair hf a b)) sorry

/-- On represented classes, the forward comparison is the Rim-Schlessinger pairing. -/
theorem liftsSelfPullbackFromProd_mk [HasRimSchlessinger p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom) (x : p.Fiber A)
    (a b : ObjectLift p f x) :
    liftsSelfPullbackFromProd f hf x (Quotient.mk'' a, Quotient.mk'' b) =
      Quotient.mk'' (liftsSelfPullbackPair hf a b) := sorry

/-- The bijection `Lift(x, A') × Lift(x, A') ≃ Lift(x, A' ×_A A')` on isomorphism
classes of lifts, for a surjection `f : A' ⟶ A` in a category cofibered in groupoids
satisfying (RS). -/
noncomputable def liftsSelfPullbackEquiv [HasRimSchlessinger p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom) (x : p.Fiber A) :
    lifts p f x × lifts p f x ≃ lifts p (selfPullbackToBase f) x where
  toFun := liftsSelfPullbackFromProd f hf x
  invFun := liftsSelfPullbackToProd f x
  left_inv := sorry
  right_inv := sorry

/-- The inverse of `liftsSelfPullbackEquiv` is the pair of projection pushforwards. -/
theorem liftsSelfPullbackEquiv_symm_apply [HasRimSchlessinger p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom) (x : p.Fiber A)
    (c : lifts p (selfPullbackToBase f) x) :
    (liftsSelfPullbackEquiv f hf x).symm c = liftsSelfPullbackToProd f x c := sorry

/-- Applying `liftsSelfPullbackEquiv` and then the projection pairing recovers the
original pair of lift classes. -/
theorem liftsSelfPullbackEquiv_apply_spec [HasRimSchlessinger p]
    (f : A' ⟶ A) (hf : Function.Surjective f.hom) (x : p.Fiber A)
    (ab : lifts p f x × lifts p f x) :
    liftsSelfPullbackToProd f x (liftsSelfPullbackEquiv f hf x ab) = ab := sorry

end CategoryTheory.Functor
