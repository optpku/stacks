module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SelfPullbackComparison
public import ReasLib.CategoryTheory.Fibered.Lifts.BaseIso
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory

/-!
# Lifts along the self-pullback comparison

The residue-plus-difference isomorphism identifies lift classes over a self-pullback
with lift classes over the corresponding square-zero pullback.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor IsLocalRing

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

/-- The residue-plus-difference comparison induces an equivalence between lifts over
an annihilated-kernel self-pullback and its square-zero pullback. -/
noncomputable def liftsSelfPullbackIsoEquiv [IsDeformationCategory p]
    {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) :
    lifts p (selfPullbackToBase f) x ≃
      lifts p (squareZeroPullbackToBase A' (kerModule f hI) f) x :=
  liftsCongr (selfPullbackIso f hI) (selfPullbackIso_comp_toA f hI) x

/-- `liftsSelfPullbackIsoEquiv` is `liftsCongr` of `selfPullbackIso`. -/
theorem liftsSelfPullbackIsoEquiv_spec [IsDeformationCategory p]
    {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) :
    liftsSelfPullbackIsoEquiv f hf hI x =
      liftsCongr (selfPullbackIso f hI) (selfPullbackIso_comp_toA f hI) x := sorry

/-- On a represented class, `liftsSelfPullbackIsoEquiv` applies `ObjectLift.alongBaseIso` along
`selfPullbackIso`. -/
theorem liftsSelfPullbackIsoEquiv_apply [IsDeformationCategory p]
    {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    {x : p.Fiber A} (a : ObjectLift p (selfPullbackToBase f) x) :
    liftsSelfPullbackIsoEquiv f hf hI x (Quotient.mk'' a) =
      Quotient.mk'' (ObjectLift.alongBaseIso (selfPullbackIso f hI)
        (selfPullbackIso_comp_toA f hI) a) := sorry

end CategoryTheory.Functor
