module

public import stacks_project.Chap90.«90_17_5_1_Comparison»
public import stacks_project.Chap90.«90_17_5_1_Lifts»
public import stacks_project.Chap90.Definition_90_16_8
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifts along `A' ×_A A'` versus `A' ×_k k[I]`

In the proof of Stacks Lemma 90.17.5, a surjection `f : A' ⟶ A` whose kernel `I` is
annihilated by `m_{A'}` yields a bijection of lift-sets along the isomorphism
`A' ×_A A' ≅ A' ×_k k[I]`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor IsLocalRing

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

/-- Deformation categories are cofibered in groupoids, so `p.op` is fibered in groupoids. -/
instance instIsFiberedInGroupoids_ofIsDeformationCategory [IsDeformationCategory p] :
    IsFibered.InGroupoids p.op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- 90.17.5.1 The bijection Lift(x, A' ×_A A') ⟶ Lift(x, A' ×_k k[I]) induced by the
ring isomorphism (a1, a2) ↦ (a1, g(a1, a2)) with g(a1, a2) = residue(a1) ⊕ (a2 - a1),
which commutes with first projections to A' and hence with the structure maps to A. -/
@[stacks 06TA]
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
