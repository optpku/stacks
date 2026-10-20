module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc.Stability

/-!
# Stability of fpqc covering families of algebraic spaces

Fpqc covering families of algebraic spaces are stable under singleton
isomorphisms, dependent composition, and slice base change along an arbitrary
morphism.
-/

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 73.9.3 (1): an isomorphism gives a singleton fpqc covering. -/
#check (AlgebraicGeometry.AlgebraicSpace.fpqcCovering_singleton_of_isIso :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X) [IsIso f],
    FpqcCovering (fun _ : Unit ↦ Over.mk f))

/- Lemma 73.9.3 (2): indexed composition preserves fpqc coverings. -/
#check (AlgebraicGeometry.AlgebraicSpace.fpqcCovering_comp :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {κ : ι → Type w} (family : ι → Over X)
    (refinement : (i : ι) → κ i → Over (family i).left),
    FpqcCovering family → (∀ i, FpqcCovering (refinement i)) →
      FpqcCovering (fun p : Sigma κ ↦
        Over.mk ((refinement p.1 p.2).hom ≫ (family p.1).hom)))

/- Lemma 73.9.3 (3): pullback preserves fpqc coverings. -/
#check (AlgebraicGeometry.AlgebraicSpace.fpqcCovering_pullback :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    {ι : Type v} (family : ι → Over X),
    FpqcCovering family → ∀ (f : X' ⟶ X),
      FpqcCovering (fun i : ι ↦ (overPullback f).obj (family i)))

end AlgebraicGeometry.AlgebraicSpace
