module

public import stacks_project.Chap73.Definition_73_8_1_PhCovering

/-!
# Stability of ph covering families of algebraic spaces

Ph covering families of algebraic spaces are stable under singleton
isomorphisms, dependent composition, and slice base change along an arbitrary
morphism.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 73.8.4 (1): if `f : X' ⟶ X` is an isomorphism of algebraic spaces over a
scheme `S`, then the singleton family `{X' ⟶ X}` is a ph covering of `X`. -/
@[stacks 0DFJ]
theorem phCovering_singleton_of_isIso {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} (f : X' ⟶ X) [IsIso f] :
    PhCovering (fun _ : Unit ↦ X') (fun _ ↦ f) :=
  sorry

/-- Lemma 73.8.4 (2): if `{X_i ⟶ X}` is a ph covering and each `{X_{ij} ⟶ X_i}`
is a ph covering, then the `Sigma`-indexed composites `{X_{ij} ⟶ X}` form a ph
covering of `X`. -/
@[stacks 0DFJ]
theorem phCovering_comp {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {κ : ι → Type w} {Xi : ι → AlgebraicSpace S}
    (f : ∀ i, Xi i ⟶ X) {Xij : (i : ι) → κ i → AlgebraicSpace S}
    (g : (i : ι) → (j : κ i) → Xij i j ⟶ Xi i)
    [PhCovering Xi f] [∀ i, PhCovering (Xij i) (g i)] :
    PhCovering (fun p : Sigma κ ↦ Xij p.1 p.2) (fun p ↦ g p.1 p.2 ≫ f p.1) :=
  sorry

/-- Lemma 73.8.4 (3): if `{X_i ⟶ X}` is a ph covering and `g : X' ⟶ X` is a
morphism of algebraic spaces, then `{X' ×_X X_i ⟶ X'}` is a ph covering. -/
@[stacks 0DFJ]
theorem phCovering_pullback {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    {ι : Type v} {Xi : ι → AlgebraicSpace S} (f : ∀ i, Xi i ⟶ X)
    [PhCovering Xi f] (g : X' ⟶ X) :
    PhCovering (fun i ↦ overPullbackObj g (Over.mk (f i)))
      (fun i ↦ overPullbackSnd g (Over.mk (f i))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
