/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Logic.Equiv.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger
public import ReasLib.CategoryTheory.Fibered.Lifts
public import ReasLib.CategoryTheory.Fibered.StronglyCocartesian.Chosen

/-!
# Lift classes along fibre squares

Under the Rim-Schlessinger condition, a fibre square in `ArtinianLocalAlgCat`
with a surjective leg induces bijections on isomorphism classes of lifts.
-/

@[expose] public section

open CategoryTheory
open Functor Fiber

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

/-- The Rim-Schlessinger condition includes cofiberedness in groupoids. -/
instance instIsFiberedInGroupoids_hasRimSchlessinger [HasRimSchlessinger p] :
    IsFibered.InGroupoids p.op :=
  HasRimSchlessinger.isCofiberedInGroupoids


/-- Reindex a lift along an equality of base morphisms. The underlying total morphism
is unchanged. -/
def objectLiftOfEq {R S : ArtinianLocalAlgCat Λ k} {f g : R ⟶ S} (h : f = g)
    {x : p.Fiber S} (a : ObjectLift p f x) : ObjectLift p g x :=
  ⟨a.val, sorry⟩

/-- `objectLiftOfEq` preserves the underlying total morphism. -/
theorem objectLiftOfEq_hom {R S : ArtinianLocalAlgCat Λ k} {f g : R ⟶ S} (h : f = g)
    {x : p.Fiber S} (a : ObjectLift p f x) :
    (objectLiftOfEq h a).hom = a.hom := sorry

/-- Transport isomorphism classes of lifts along an equality of base morphisms. -/
noncomputable def liftsReindex {R S : ArtinianLocalAlgCat Λ k} {f g : R ⟶ S}
    (h : f = g) {x : p.Fiber S} : lifts p f x ≃ lifts p g x where
  toFun := Quotient.lift (fun a ↦ Quotient.mk'' (objectLiftOfEq h a)) sorry
  invFun := Quotient.lift (fun a ↦ Quotient.mk'' (objectLiftOfEq h.symm a)) sorry
  left_inv := sorry
  right_inv := sorry

/-- On a represented class, `liftsReindex` is `objectLiftOfEq` of the representative. -/
theorem liftsReindex_apply {R S : ArtinianLocalAlgCat Λ k} {f g : R ⟶ S} (h : f = g)
    {x : p.Fiber S} (a : ObjectLift p f x) :
    liftsReindex h (Quotient.mk'' a) = Quotient.mk'' (objectLiftOfEq h a) := sorry

/-- A lift along a surjection in `ArtinianLocalAlgCat` has surjective image under `p`. -/
theorem objectLift_image_surjective {A B : ArtinianLocalAlgCat Λ k} {f : A ⟶ B}
    (hf : Function.Surjective f.hom) {x : p.Fiber B} (a : ObjectLift p f x) :
    Function.Surjective (p.map a.hom).hom := sorry


/-- Reindexing the domain of `u` by `eqToHom` preserves the hom-lift of a lift along
`u ≫ f`. -/
instance instIsHomLift_pushDomain {P B A : ArtinianLocalAlgCat Λ k}
    (u : P ⟶ B) (f : B ⟶ A) {x : p.Fiber A} (a : ObjectLift p (u ≫ f) x) :
    p.IsHomLift ((eqToHom (IsHomLift.domain_eq p (u ≫ f) a.hom) ≫ u) ≫ f) a.hom :=
  sorry

/-- Push a lift of `x` along `u ≫ f` forward along `u`, obtaining a lift along `f`. -/
noncomputable def objectLiftPushforward [IsFibered.InGroupoids p.op]
    {P B A : ArtinianLocalAlgCat Λ k} (u : P ⟶ B) (f : B ⟶ A) {x : p.Fiber A}
    (a : ObjectLift p (u ≫ f) x) : ObjectLift p f x :=
  let u' : p.obj a.left ⟶ B :=
    eqToHom (IsHomLift.domain_eq p (u ≫ f) a.hom) ≫ u
  let l := IsPreFibered.pullbackMap (p := p.op) (a := Opposite.op a.left) rfl u'.op
  ⟨Over.mk
      (@IsStronglyCocartesian.map _ _ _ _ p _ _ _ _ u' l.unop
        (inferInstance : p.IsStronglyCocartesian u' l.unop)
        _ _ _ _ (rfl : u' ≫ f = u' ≫ f) a.hom inferInstance), sorry⟩

/-- Pushing a lift forward along `u` yields a lift of the same fibre object along `f`. -/
theorem objectLiftPushforward_spec [IsFibered.InGroupoids p.op]
    {P B A : ArtinianLocalAlgCat Λ k} (u : P ⟶ B) (f : B ⟶ A) {x : p.Fiber A}
    (a : ObjectLift p (u ≫ f) x) :
    p.IsHomLift f (objectLiftPushforward u f a).hom ∧
      p.obj (objectLiftPushforward u f a).left = B := sorry

/-- If `ρ1` and `ρ2` commute with the underlying lifts `a1` and `a2`, then the
induced maps into the cospan `A1 ⟶ A ← A2` agree. -/
theorem liftsPullback_lift_comp_eq {A A1 A2 : ArtinianLocalAlgCat Λ k}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {x : p.Fiber A}
    (a1 : ObjectLift p f1 x) (a2 : ObjectLift p f2 x)
    {w : F} (ρ1 : w ⟶ a1.left) (ρ2 : w ⟶ a2.left)
    (h_comm : ρ1 ≫ a1.hom = ρ2 ≫ a2.hom) :
    (p.map ρ1 ≫ eqToHom (IsHomLift.domain_eq p f1 a1.hom)) ≫ f1 =
      (p.map ρ2 ≫ eqToHom (IsHomLift.domain_eq p f2 a2.hom)) ≫ f2 := sorry

/-- Compose a lift of `a1.domain` along `π1` with the lift `a1` of `x`. -/
def objectLiftComp {A A1 P : ArtinianLocalAlgCat Λ k} {f1 : A1 ⟶ A} {π1 : P ⟶ A1}
    {x : p.Fiber A} (a1 : ObjectLift p f1 x) (b : ObjectLift p π1 a1.domain) :
    ObjectLift p (π1 ≫ f1) x :=
  ⟨Over.mk (b.hom ≫ a1.hom), sorry⟩

/-- The composite lift is the composite of the underlying total morphisms. -/
theorem objectLiftComp_hom {A A1 P : ArtinianLocalAlgCat Λ k} {f1 : A1 ⟶ A} {π1 : P ⟶ A1}
    {x : p.Fiber A} (a1 : ObjectLift p f1 x) (b : ObjectLift p π1 a1.domain) :
    (objectLiftComp a1 b).hom = b.hom ≫ a1.hom := sorry

/-- The Rim-Schlessinger pairing of lifts of `x` along the two legs of a fibre square
with surjective second leg, as a lift along `π1 ≫ f1`. -/
noncomputable def liftsPullbackPair [HasRimSchlessinger p]
    {A A1 A2 P : ArtinianLocalAlgCat Λ k}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hP : IsPullback π1 π2 f1 f2) (hf2 : Function.Surjective f2.hom)
    {x : p.Fiber A} (a1 : ObjectLift p f1 x) (a2 : ObjectLift p f2 x) :
    ObjectLift p (π1 ≫ f1) x :=
  let h := (inferInstance : HasRimSchlessinger p).exists_pullback a1.hom a2.hom
    (objectLift_image_surjective hf2 a2)
  let w := Classical.choose h
  let ρ1 := Classical.choose (Classical.choose_spec h)
  let ρ2 := Classical.choose (Classical.choose_spec (Classical.choose_spec h))
  let hPB := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))).1
  let g1 : p.obj w ⟶ A1 := p.map ρ1 ≫ eqToHom (IsHomLift.domain_eq p f1 a1.hom)
  let g2 : p.obj w ⟶ A2 := p.map ρ2 ≫ eqToHom (IsHomLift.domain_eq p f2 a2.hom)
  objectLiftPushforward (hP.lift g1 g2 (liftsPullback_lift_comp_eq a1 a2 ρ1 ρ2 hPB.w))
    (π1 ≫ f1) ⟨Over.mk (ρ1 ≫ a1.hom), sorry⟩

/-- The forward comparison sending a pair of lift classes along the two legs to a
lift class along `π1 ≫ f1`. -/
noncomputable def liftsPullbackFromProd [HasRimSchlessinger p]
    {A A1 A2 P : ArtinianLocalAlgCat Λ k}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hP : IsPullback π1 π2 f1 f2) (hf2 : Function.Surjective f2.hom)
    (x : p.Fiber A) :
    lifts p f1 x × lifts p f2 x → lifts p (π1 ≫ f1) x :=
  fun ab ↦
    Quotient.liftOn₂ ab.1 ab.2
      (fun a b ↦ Quotient.mk'' (liftsPullbackPair hP hf2 a b)) sorry

/-- On represented classes, the forward comparison is the Rim-Schlessinger pairing. -/
theorem liftsPullbackFromProd_mk [HasRimSchlessinger p]
    {A A1 A2 P : ArtinianLocalAlgCat Λ k}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hP : IsPullback π1 π2 f1 f2) (hf2 : Function.Surjective f2.hom)
    (x : p.Fiber A) (a1 : ObjectLift p f1 x) (a2 : ObjectLift p f2 x) :
    liftsPullbackFromProd hP hf2 x (Quotient.mk'' a1, Quotient.mk'' a2) =
      Quotient.mk'' (liftsPullbackPair hP hf2 a1 a2) := sorry

/-- The inverse comparison sending a lift along `π1 ≫ f1` to the pair of its
pushforwards along the two projections. -/
noncomputable def liftsPullbackToProd [IsFibered.InGroupoids p.op]
    {A A1 A2 P : ArtinianLocalAlgCat Λ k}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hP : IsPullback π1 π2 f1 f2) (x : p.Fiber A) :
    lifts p (π1 ≫ f1) x → lifts p f1 x × lifts p f2 x :=
  Quotient.lift
    (fun a ↦
      (Quotient.mk'' (objectLiftPushforward π1 f1 a),
        Quotient.mk'' (objectLiftPushforward π2 f2 (objectLiftOfEq hP.w a))))
    sorry

/-- On a represented class, `liftsPullbackToProd` is the pair of projection
pushforwards. -/
theorem liftsPullbackToProd_mk [IsFibered.InGroupoids p.op]
    {A A1 A2 P : ArtinianLocalAlgCat Λ k}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hP : IsPullback π1 π2 f1 f2) (x : p.Fiber A)
    (a : ObjectLift p (π1 ≫ f1) x) :
    liftsPullbackToProd hP x (Quotient.mk'' a) =
      (Quotient.mk'' (objectLiftPushforward π1 f1 a),
        Quotient.mk'' (objectLiftPushforward π2 f2 (objectLiftOfEq hP.w a))) :=
  sorry

/-- The bijection `Lift(x, A1) × Lift(x, A2) ≃ Lift(x, A1 ×_A A2)` on isomorphism
classes of lifts, for a fibre square with either `A1 ⟶ A` or `A2 ⟶ A` surjective. -/
noncomputable def liftsPullbackProdEquiv [HasRimSchlessinger p]
    {A A1 A2 P : ArtinianLocalAlgCat Λ k}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hP : IsPullback π1 π2 f1 f2)
    (hsurj : Function.Surjective f1.hom ∨ Function.Surjective f2.hom)
    (x : p.Fiber A) :
    lifts p f1 x × lifts p f2 x ≃ lifts p (π1 ≫ f1) x where
  toFun ab :=
    @dite _ (Function.Surjective f2.hom) (Classical.propDecidable _)
      (fun hf2 ↦ liftsPullbackFromProd hP hf2 x ab)
      (fun hnot ↦
        liftsReindex hP.w.symm
          (liftsPullbackFromProd hP.flip (Or.resolve_right hsurj hnot) x (ab.2, ab.1)))
  invFun := liftsPullbackToProd hP x
  left_inv := sorry
  right_inv := sorry

/-- Applying `liftsPullbackProdEquiv` to represented classes is the Rim-Schlessinger
pairing along a surjective second leg, after flipping if needed. -/
theorem liftsPullbackProdEquiv_apply [HasRimSchlessinger p]
    {A A1 A2 P : ArtinianLocalAlgCat Λ k}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hP : IsPullback π1 π2 f1 f2)
    (hsurj : Function.Surjective f1.hom ∨ Function.Surjective f2.hom)
    (x : p.Fiber A) (ab : lifts p f1 x × lifts p f2 x) :
    liftsPullbackProdEquiv hP hsurj x ab =
      @dite _ (Function.Surjective f2.hom) (Classical.propDecidable _)
        (fun hf2 ↦ liftsPullbackFromProd hP hf2 x ab)
        (fun hnot ↦
          liftsReindex hP.w.symm
            (liftsPullbackFromProd hP.flip (Or.resolve_right hsurj hnot) x
              (ab.2, ab.1))) := sorry

/-- The inverse of `liftsPullbackProdEquiv` is the pair of projection pushforwards. -/
theorem liftsPullbackProdEquiv_symm_apply [HasRimSchlessinger p]
    {A A1 A2 P : ArtinianLocalAlgCat Λ k}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hP : IsPullback π1 π2 f1 f2)
    (hsurj : Function.Surjective f1.hom ∨ Function.Surjective f2.hom)
    (x : p.Fiber A) (c : lifts p (π1 ≫ f1) x) :
    (liftsPullbackProdEquiv hP hsurj x).symm c = liftsPullbackToProd hP x c := sorry

/-- Applying `liftsPullbackProdEquiv` and then the projection pairing recovers the
original pair of lift classes. -/
theorem liftsPullbackProdEquiv_spec [HasRimSchlessinger p]
    {A A1 A2 P : ArtinianLocalAlgCat Λ k}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hP : IsPullback π1 π2 f1 f2)
    (hsurj : Function.Surjective f1.hom ∨ Function.Surjective f2.hom)
    (x : p.Fiber A) (ab : lifts p f1 x × lifts p f2 x) :
    liftsPullbackToProd hP x (liftsPullbackProdEquiv hP hsurj x ab) = ab := sorry

/-- The Rim-Schlessinger pairing of a fixed lift `a1` with a lift along `f2`, as a
lift of `a1.domain` along `π1`. -/
noncomputable def liftsPullbackSlicePair [HasRimSchlessinger p]
    {A A1 A2 P : ArtinianLocalAlgCat Λ k}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hP : IsPullback π1 π2 f1 f2)
    (hsurj : Function.Surjective f1.hom ∨ Function.Surjective f2.hom)
    {x : p.Fiber A} (a1 : ObjectLift p f1 x) (a2 : ObjectLift p f2 x) :
    ObjectLift p π1 a1.domain :=
  @dite _ (Function.Surjective f2.hom) (Classical.propDecidable _)
    (fun hf2 ↦
      let h := (inferInstance : HasRimSchlessinger p).exists_pullback a1.hom a2.hom
        (objectLift_image_surjective hf2 a2)
      let w := Classical.choose h
      let ρ1 := Classical.choose (Classical.choose_spec h)
      let ρ2 := Classical.choose (Classical.choose_spec (Classical.choose_spec h))
      let hPB := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))).1
      let g1 : p.obj w ⟶ A1 := p.map ρ1 ≫ eqToHom (IsHomLift.domain_eq p f1 a1.hom)
      let g2 : p.obj w ⟶ A2 := p.map ρ2 ≫ eqToHom (IsHomLift.domain_eq p f2 a2.hom)
      objectLiftPushforward (hP.lift g1 g2 (liftsPullback_lift_comp_eq a1 a2 ρ1 ρ2 hPB.w))
        π1 ⟨Over.mk ρ1, sorry⟩)
    (fun hnot ↦
      let hf1 := Or.resolve_right hsurj hnot
      let h := (inferInstance : HasRimSchlessinger p).exists_pullback a2.hom a1.hom
        (objectLift_image_surjective hf1 a1)
      let w := Classical.choose h
      let ρ2 := Classical.choose (Classical.choose_spec h)
      let ρ1 := Classical.choose (Classical.choose_spec (Classical.choose_spec h))
      let hPB := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))).1
      let g1 : p.obj w ⟶ A1 := p.map ρ1 ≫ eqToHom (IsHomLift.domain_eq p f1 a1.hom)
      let g2 : p.obj w ⟶ A2 := p.map ρ2 ≫ eqToHom (IsHomLift.domain_eq p f2 a2.hom)
      objectLiftPushforward
        (hP.lift g1 g2 (liftsPullback_lift_comp_eq a1 a2 ρ1 ρ2 hPB.w.symm))
        π1 ⟨Over.mk ρ1, sorry⟩)

/-- The bijection `Lift(x1, A1 ×_A A2) ≃ Lift(x, A2)` on isomorphism classes of
lifts, for a fixed lift `a1` of `x` along `A1 ⟶ A`. -/
noncomputable def liftsPullbackSliceEquiv [HasRimSchlessinger p]
    {A A1 A2 P : ArtinianLocalAlgCat Λ k}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hP : IsPullback π1 π2 f1 f2)
    (hsurj : Function.Surjective f1.hom ∨ Function.Surjective f2.hom)
    {x : p.Fiber A} (a1 : ObjectLift p f1 x) :
    lifts p π1 a1.domain ≃ lifts p f2 x where
  toFun q :=
    (liftsPullbackToProd hP x
      (Quotient.lift (fun b ↦ Quotient.mk'' (objectLiftComp a1 b)) sorry q)).2
  invFun q :=
    Quotient.lift (fun a2 ↦ Quotient.mk'' (liftsPullbackSlicePair hP hsurj a1 a2))
      sorry q
  left_inv := sorry
  right_inv := sorry

/-- On a represented class, the forward map of `liftsPullbackSliceEquiv` is the
second projection of `liftsPullbackToProd` after composing with `a1`. -/
theorem liftsPullbackSliceEquiv_apply [HasRimSchlessinger p]
    {A A1 A2 P : ArtinianLocalAlgCat Λ k}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hP : IsPullback π1 π2 f1 f2)
    (hsurj : Function.Surjective f1.hom ∨ Function.Surjective f2.hom)
    {x : p.Fiber A} (a1 : ObjectLift p f1 x) (b : ObjectLift p π1 a1.domain) :
    liftsPullbackSliceEquiv hP hsurj a1 (Quotient.mk'' b) =
      (liftsPullbackToProd hP x (Quotient.mk'' (objectLiftComp a1 b))).2 := sorry

/-- On a represented class, the inverse of `liftsPullbackSliceEquiv` is the sliced
Rim-Schlessinger pairing. -/
theorem liftsPullbackSliceEquiv_symm_apply [HasRimSchlessinger p]
    {A A1 A2 P : ArtinianLocalAlgCat Λ k}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (hP : IsPullback π1 π2 f1 f2)
    (hsurj : Function.Surjective f1.hom ∨ Function.Surjective f2.hom)
    {x : p.Fiber A} (a1 : ObjectLift p f1 x) (a2 : ObjectLift p f2 x) :
    (liftsPullbackSliceEquiv hP hsurj a1).symm (Quotient.mk'' a2) =
      Quotient.mk'' (liftsPullbackSlicePair hP hsurj a1 a2) := sorry

/-- The composite bijection
`Lift(x1, A1' ×_A A2) ≃ Lift(x1, A1') × Lift(x, A2)` along a composite of fibre
squares with `A1' ⟶ A1` and `A1 ⟶ A` surjective. -/
noncomputable def liftsPullbackCompEquiv [HasRimSchlessinger p]
    {A A1 A2 A1' P Q : ArtinianLocalAlgCat Λ k}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {f1' : A1' ⟶ A1}
    {π1 : P ⟶ A1} {π2 : P ⟶ A2} {σ1 : Q ⟶ A1'} {σ2 : Q ⟶ P}
    (hP : IsPullback π1 π2 f1 f2) (hQ : IsPullback σ1 σ2 f1' π1)
    (hf1 : Function.Surjective f1.hom) (hf1' : Function.Surjective f1'.hom)
    {x : p.Fiber A} (a1 : ObjectLift p f1 x) :
    lifts p (σ1 ≫ f1') a1.domain ≃ lifts p f1' a1.domain × lifts p f2 x :=
  (liftsPullbackProdEquiv hQ (Or.inl hf1') a1.domain).symm.trans
    (Equiv.prodCongr (Equiv.refl _) (liftsPullbackSliceEquiv hP (Or.inl hf1) a1))

/-- `liftsPullbackCompEquiv` is the product bijection of the upper square, inverted,
followed by the slice bijection of the lower square on the second factor. -/
theorem liftsPullbackCompEquiv_spec [HasRimSchlessinger p]
    {A A1 A2 A1' P Q : ArtinianLocalAlgCat Λ k}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {f1' : A1' ⟶ A1}
    {π1 : P ⟶ A1} {π2 : P ⟶ A2} {σ1 : Q ⟶ A1'} {σ2 : Q ⟶ P}
    (hP : IsPullback π1 π2 f1 f2) (hQ : IsPullback σ1 σ2 f1' π1)
    (hf1 : Function.Surjective f1.hom) (hf1' : Function.Surjective f1'.hom)
    {x : p.Fiber A} (a1 : ObjectLift p f1 x) :
    liftsPullbackCompEquiv hP hQ hf1 hf1' a1 =
      (liftsPullbackProdEquiv hQ (Or.inl hf1') a1.domain).symm.trans
        (Equiv.prodCongr (Equiv.refl _)
          (liftsPullbackSliceEquiv hP (Or.inl hf1) a1)) :=
  rfl

end CategoryTheory.Functor
