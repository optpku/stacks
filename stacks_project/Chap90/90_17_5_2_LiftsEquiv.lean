module

public import stacks_project.Chap90.«90_17_5_2_SelfPullback»
public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger
public import stacks_project.Chap90.Definition_90_17_1_ObjectLift
public import stacks_project.Chap90.Remarks_90_5_2_Pushforward

/-!
# Lifts of an object to a self fibre product

Under the Rim-Schlessinger condition, isomorphism classes of lifts of `x` along a
surjection `f : A' ⟶ A` pair to isomorphism classes of lifts of `x` along
`A' ×_A A' ⟶ A`.
-/

@[expose] public section

open CategoryTheory
open Functor Fiber ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

variable {A A' : ArtinianLocalAlgCat Λ k}

/-- The Rim-Schlessinger condition includes cofiberedness in groupoids. -/
instance instIsFiberedInGroupoids_ofHasRimSchlessinger [HasRimSchlessinger p] :
    IsFibered.InGroupoids p.op :=
  HasRimSchlessinger.isCofiberedInGroupoids

/-- Reindex a lift along an equality of base morphisms. The underlying total morphism
is unchanged. -/
def ObjectLift.congr {R S : ArtinianLocalAlgCat Λ k} {f g : R ⟶ S} (h : f = g)
    {x : p.Fiber S} (a : ObjectLift p f x) : ObjectLift p g x :=
  ⟨a.val, sorry⟩

/-- `ObjectLift.congr` preserves the underlying total morphism. -/
theorem ObjectLift.congr_hom {R S : ArtinianLocalAlgCat Λ k} {f g : R ⟶ S} (h : f = g)
    {x : p.Fiber S} (a : ObjectLift p f x) :
    (ObjectLift.congr h a).hom = a.hom := sorry

/-- The strongly cocartesian property of a bundled lift is a typeclass instance. -/
instance instIsStronglyCocartesian_lift {x : F} {V : ArtinianLocalAlgCat Λ k}
    {g : p.obj x ⟶ V} (l : StronglyCocartesianLift p g) :
    p.IsStronglyCocartesian g l.hom :=
  l.isStronglyCocartesian

/-- Reindexing the domain of `u` by `eqToHom` preserves the hom-lift of a lift along
`u ≫ f`. -/
instance instIsHomLift_reindexed {P : ArtinianLocalAlgCat Λ k}
    (u : P ⟶ A') (f : A' ⟶ A) {x : p.Fiber A} (a : ObjectLift p (u ≫ f) x) :
    p.IsHomLift ((eqToHom (IsHomLift.domain_eq p (u ≫ f) a.hom) ≫ u) ≫ f) a.hom :=
  sorry

/-- Push a lift of `x` along `u ≫ f` forward along `u`, obtaining a lift along `f`. -/
noncomputable def ObjectLift.pushforwardAlong [IsFibered.InGroupoids p.op]
    {P : ArtinianLocalAlgCat Λ k} (u : P ⟶ A') (f : A' ⟶ A) {x : p.Fiber A}
    (a : ObjectLift p (u ≫ f) x) : ObjectLift p f x :=
  let u' : p.obj a.left ⟶ A' :=
    eqToHom (IsHomLift.domain_eq p (u ≫ f) a.hom) ≫ u
  let l := StronglyCocartesianLift.ofCleavage (cleavageOp p) u'
  ⟨Over.mk (IsStronglyCocartesian.map p u' l.hom (rfl : u' ≫ f = u' ≫ f) a.hom), sorry⟩

/-- Pushing a lift forward along `u` yields a lift of the same fibre object along `f`. -/
theorem ObjectLift.pushforwardAlong_spec [IsFibered.InGroupoids p.op]
    {P : ArtinianLocalAlgCat Λ k} (u : P ⟶ A') (f : A' ⟶ A) {x : p.Fiber A}
    (a : ObjectLift p (u ≫ f) x) :
    p.IsHomLift f (ObjectLift.pushforwardAlong u f a).hom ∧
      p.obj (ObjectLift.pushforwardAlong u f a).left = A' := sorry

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
