module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.Henselian
public import Mathlib.Topology.Defs.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Spec.IdealSubobject
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints

/-!
# Lifting a proper clopen from the special fibre over a henselian pair

If `(A, I)` is a henselian pair and `X` is separated of finite type over `A`, a
clopen subspace of the special fibre that is proper over `Spec(A ⧸ I)` lifts to a
clopen subspace of `X` proper over `A`.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {A : Type u} [CommRing A]

/-- The morphism `Spec(A ⧸ I) ⟶ Spec A`, as algebraic spaces over `Spec A`. -/
abbrev specQuotientι (I : Ideal A) :
    ofOver (Over.mk (@Spec.quotientMap (CommRingCat.of A) I)) ⟶
      ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))) :=
  ofOverHomMk (@Spec.quotientMap (CommRingCat.of A) I)
    (Category.comp_id (@Spec.quotientMap (CommRingCat.of A) I))

/-- `specQuotientι I` is `ofOverHomMk` of `Spec.quotientMap I`. -/
theorem specQuotientι_eq (I : Ideal A) :
    specQuotientι I =
      ofOverHomMk (@Spec.quotientMap (CommRingCat.of A) I)
        (Category.comp_id (@Spec.quotientMap (CommRingCat.of A) I)) :=
  sorry

/-- The special fibre `X₀ = X ×_{Spec A} Spec(A ⧸ I)`, as an algebraic space over
`Spec A`. -/
abbrev fiberOverQuotient (I : Ideal A) (X : AlgebraicSpace (Spec (CommRingCat.of A))) :
    AlgebraicSpace (Spec (CommRingCat.of A)) :=
  pullback (toBase X) (specQuotientι I)

/-- `fiberOverQuotient I X` is the fibre product of `toBase X` with `specQuotientι I`. -/
theorem fiberOverQuotient_eq (I : Ideal A)
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) :
    fiberOverQuotient I X = pullback (toBase X) (specQuotientι I) :=
  sorry

/-- Lemma 76.36.10: Let `(A, I)` be a henselian pair. Let `X` be an algebraic space
separated and of finite type over `A`. Set `X₀ = X ×_{Spec A} Spec(A ⧸ I)`. Let
`Y ⊂ X₀` be an open and closed subspace such that `Y ⟶ Spec(A ⧸ I)` is proper.
Then there exists an open and closed subspace `W ⊂ X` which is proper over `A`
with `W ×_{Spec A} Spec(A ⧸ I) = Y`.

The fibre-product equality is the comparison isomorphism of `Y` with
`W ×_X X₀` over `X₀`. -/
@[stacks 0CWI]
theorem exists_clopen_proper_lift (I : Ideal A) [HenselianRing A I]
    (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    [Separated (toBase X)] [FiniteType (toBase X)]
    (Y : OpenSubspace (fiberOverQuotient I X)) (hY : IsClopen Y.pointsSet)
    [Proper (Y.ι ≫ pullback.snd (toBase X) (specQuotientι I))] :
    ∃ (W : OpenSubspace X)
      (e : Y.X ≅ pullback W.ι (pullback.fst (toBase X) (specQuotientι I))),
      IsClopen W.pointsSet ∧ Proper (W.ι ≫ toBase X) ∧
        e.hom ≫ pullback.snd W.ι (pullback.fst (toBase X) (specQuotientι I)) =
          Y.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
