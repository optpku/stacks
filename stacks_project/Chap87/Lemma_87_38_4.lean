module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import stacks_project.Chap87.Lemma_87_38_4_Completion
public import stacks_project.Chap87.Lemma_87_38_5_Types

/-!
# Types of the affine formal completion along a closed subscheme

For an affine scheme `X = Spec(A)` over `S` and a closed subscheme
`Z = Spec(A ⧸ I)`, the completion `X^∧_Z` is `spfAdicCompletion`. It is always
weakly adic, equals `Spf` of the `I`-adic completion when `I` is finitely
generated, is adic* under that same finite-generation hypothesis, and is
Noetherian when `X` is Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The closed immersion `Spec(A ⧸ I) ⟶ Spec(A)` is locally of finite
presentation if and only if `I` is finitely generated. -/
theorem finitePresentation_closedImmersion_iff {A : Type u} [CommRing A]
    (I : Ideal A) :
    LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ↔ I.FG :=
  sorry

/-- Lemma 87.38.4 (1): Let `S` be a scheme, let `X = Spec(A)` be an affine scheme
over `S`, and let `Z ⊂ X` be the closed subscheme corresponding to `I ⊂ A`.
The affine formal algebraic space `spfAdicCompletion structureHom I` is weakly
adic. -/
@[stacks 0GXX]
instance instIsWeaklyAdic_spfAdicCompletion {S : Scheme.{u}} {A : Type u}
    [CommRing A] (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    IsWeaklyAdic (spfAdicCompletion structureHom I) :=
  sorry

/-- Lemma 87.38.4 (2): In the situation of Lemma 87.38.4 (1), if `I` is finitely
generated, then `spfAdicCompletion structureHom I` equals `Spf` of the `I`-adic
completion of `A`. -/
@[stacks 0GXX]
theorem isIso_toSpfAdic_of_fg {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (hI : I.FG) :
    IsIso (toSpfAdic_of_fg structureHom I hI) :=
  sorry

/-- Lemma 87.38.4 (3): In the situation of Lemma 87.38.4 (1), if `Z → X` is of
finite presentation, i.e., `I` is finitely generated, then
`spfAdicCompletion structureHom I` is adic*. -/
@[stacks 0GXX]
theorem isAdicStar_of_fg {S : Scheme.{u}} {A : Type u} [CommRing A]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) (hI : I.FG) :
    IsAdicStarAffine (spfAdicCompletion structureHom I) :=
  sorry

/-- Lemma 87.38.4 (4): In the situation of Lemma 87.38.4 (1), if `X` is
Noetherian, then `spfAdicCompletion structureHom I` is Noetherian. -/
@[stacks 0GXX]
instance instIsNoetherianAffine_spfAdicCompletion {S : Scheme.{u}} {A : Type u}
    [CommRing A] [IsNoetherian (Spec (.of A))]
    (structureHom : Spec (.of A) ⟶ S) (I : Ideal A) :
    IsNoetherianAffine (spfAdicCompletion structureHom I) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
