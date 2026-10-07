module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap73.Definition_73_5_1_Covering

/-!
# Stability of smooth covering families of algebraic spaces

Smooth covering families of algebraic spaces are stable under singleton
isomorphisms, indexed composition, and base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 73.5.3 (1): if `f : X' ⟶ X` is an isomorphism of algebraic spaces over a
scheme `S`, then the singleton family `Over.mk f` is a smooth covering of `X`. -/
@[stacks 041D]
theorem smoothCovering_singleton_of_isIso {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} (f : X' ⟶ X) [IsIso f] :
    SmoothCovering (fun _ : Unit ↦ Over.mk f) :=
  sorry

/-- Lemma 73.5.3 (2): if `Xfam` is a smooth covering of `X` and each `Y i` is a
smooth covering of `(Xfam i).left`, then the `Sigma`-indexed composites
`(Y p.1 p.2).hom ≫ (Xfam p.1).hom` form a smooth covering of `X`. -/
@[stacks 041D]
theorem smoothCovering_comp {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {κ : ι → Type w} (Xfam : ι → Over X)
    (Y : (i : ι) → κ i → Over (Xfam i).left)
    (hX : SmoothCovering Xfam) (hY : ∀ i, SmoothCovering (Y i)) :
    SmoothCovering (fun p : Sigma κ ↦
      Over.mk ((Y p.1 p.2).hom ≫ (Xfam p.1).hom)) :=
  sorry

/-- Lemma 73.5.3 (3): if `Xfam` is a smooth covering of `X` and `f : X' ⟶ X` is a
morphism of algebraic spaces, then the base-changed family
`Over.mk (pullback.fst f (Xfam i).hom)` is a smooth covering of `X'`. -/
@[stacks 041D]
theorem smoothCovering_pullback {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    {ι : Type v} (Xfam : ι → Over X) (hX : SmoothCovering Xfam) (f : X' ⟶ X) :
    SmoothCovering (fun i ↦ Over.mk (pullback.fst f (Xfam i).hom)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
