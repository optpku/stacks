/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Lifts
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Coimage
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.CospanPullback
public import ReasLib.CategoryTheory.Fibered.Lifts.Pushforward

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.LocalRing.Pullback
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal

/-!
# Self fibre products in `ArtinianLocalAlgCat`

The fibre product `A' ×_A A'` of a morphism `f : A' ⟶ A` with itself is the algebra
pullback of `f.hom` along itself, bundled as an object of `C_Λ`.
It specializes the cospan pullback using the identity of `A'`: the diagonal splits
the first projection, so no surjectivity assumption on `f` is needed.
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

/-- The residue-field algebra structure on the self fibre product. -/
abbrev selfPullbackResidueFieldAlgebra (f : A' ⟶ A) :
    Algebra Λ (ResidueField (selfPullbackSubalgebra f)) :=
  @ResidueField.algebra (selfPullbackSubalgebra f)
    _ (instIsLocalRing_cospanPullback f f) Λ inferInstance
    (@Subalgebra.algebra Λ (A'.carrier × A'.carrier) _ _
      (@Prod.algebra Λ A'.carrier A'.carrier _ _ A'.algebra _ A'.algebra)
      (selfPullbackSubalgebra f))

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
and the residue identification of `A'`. This is the cospan identification for the
identity comparison `A' ⟶ A'`, whose section is the diagonal. -/
noncomputable def selfPullbackResidueFieldIso (f : A' ⟶ A) :
    @AlgEquiv Λ (ResidueField (selfPullbackSubalgebra f)) k _ _ _
      (selfPullbackResidueFieldAlgebra f) inferInstance :=
  cospanPullbackResidueFieldIso f f (𝟙 A') (Category.id_comp f)

/-- The fibre product `A' ×_A A'`, viewed as an object of `ArtinianLocalAlgCat`. -/
noncomputable def selfPullback (f : A' ⟶ A) : ArtinianLocalAlgCat Λ k :=
  cospanPullback f f (𝟙 A') (Category.id_comp f)

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
        _ _ A'.algebra _ A'.algebra _ A.algebra f.hom f.hom) (by
          intro b
          exact congrArg (fun q : B ⟶ A ↦ q.hom b) h))
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
    selfPullbackLift f g₁ g₂ h ≫ selfPullbackFst f = g₁ := by
  apply hom_ext
  apply AlgHom.ext
  intro b
  rfl

/-- The induced lift projects to the second given map. -/
theorem selfPullbackLift_comp_snd {B : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (g₁ g₂ : B ⟶ A') (h : g₁ ≫ f = g₂ ≫ f) :
    selfPullbackLift f g₁ g₂ h ≫ selfPullbackSnd f = g₂ := by
  apply hom_ext
  apply AlgHom.ext
  intro b
  rfl

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
    Function.Surjective (p.map a.hom).hom := by
  have aux {A B : ArtinianLocalAlgCat Λ k} {a b : F}
      (f : A ⟶ B) (φ : a ⟶ b) (hφ : p.IsHomLift f φ)
      (hf : Function.Surjective f.hom) : Function.Surjective (p.map φ).hom := by
    cases hφ
    exact hf
  exact aux f a.hom a.property hf

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
  let hPB := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))).1
  let g1 : p.obj w ⟶ A' := p.map π1 ≫ eqToHom (IsHomLift.domain_eq p f a.hom)
  let g2 : p.obj w ⟶ A' := p.map π2 ≫ eqToHom (IsHomLift.domain_eq p f b.hom)
  ObjectLift.pushforwardAlong
    (selfPullbackLift f g1 g2 (liftsPullback_lift_comp_eq a b π1 π2 hPB.w))
    (selfPullbackToBase f) ⟨Over.mk (π1 ≫ a.hom), by
      let s := selfPullbackLift f g1 g2 (liftsPullback_lift_comp_eq a b π1 π2 hPB.w)
      letI : p.IsHomLift (s ≫ selfPullbackFst f) π1 := by
        apply IsHomLift.of_fac' p _ π1 rfl (IsHomLift.domain_eq p f a.hom)
        simp only [eqToHom_refl, Category.id_comp, s, selfPullbackLift_comp_fst,
          g1, Category.assoc, eqToHom_trans, Category.comp_id]
      exact (Category.assoc s (selfPullbackFst f) f) ▸
        (inferInstance : p.IsHomLift ((s ≫ selfPullbackFst f) ≫ f) (π1 ≫ a.hom))⟩

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
