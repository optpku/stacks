/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_32_1_Factorization

/-!
# Glueing factorization of an integral morphism at a closed point

Lemma 76.32.1 constructs, for an integral morphism of algebraic spaces and a
point represented by a closed immersion from the spectrum of a field, a
factorization through the relative spectrum of an explicit algebra pullback.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Lemma 76.32.1 (1): the structure morphism of the glueing space is integral. -/
@[stacks 0EDM]
instance IsIntegralHom.fromGlueing (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    IsIntegralHom (fromGlueing f p) :=
  sorry

/-- Lemma 76.32.1 (2): `X ⟶ X'` is an isomorphism over any open of `X'` complementary
to the scheme-theoretic fibre `X'_y`. -/
@[stacks 0EDM]
theorem isIso_openInverseImageTo_toGlueing (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] {U : AlgebraicSpace S}
    (ι : U ⟶ glueingSpec f p) [IsOpenImmersion ι]
    (hU : Set.range (Points.map ι) =
      (Set.range (Points.map (fiberι (fromGlueing f p) p)))ᶜ) :
    IsIso (openInverseImageTo (toGlueing f p) ι) :=
  sorry

/-- Lemma 76.32.1 (3): the scheme-theoretic fibre `X'_y` has a unique point `x'`
with residue field `κ(x') = k`. -/
@[stacks 0EDM]
theorem existsUnique_fiberPoint_eq_residueField (f : X ⟶ Y) [IsIntegralHom f]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    ∃! x' : Points (fieldFiber (fromGlueing f p) p),
      ∃ σ : ofOver p.overObj ⟶ fieldFiber (fromGlueing f p) p,
        σ ≫ fiberToSpec (fromGlueing f p) p = 𝟙 (ofOver p.overObj) ∧
          Points.mk (FieldValuedPoint.of p.K p.structureHom σ) = x' :=
  sorry

/-- Lemma 76.32.1 (4): if `f` is finite and `Y` is locally Noetherian, then the
structure morphism of the glueing space is finite. -/
@[stacks 0EDM]
instance IsFinite.fromGlueing (f : X ⟶ Y) [IsFinite f] [IsLocallyNoetherian Y]
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    IsFinite (fromGlueing f p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
