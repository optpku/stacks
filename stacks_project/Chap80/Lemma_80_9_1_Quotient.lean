/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantSpectrum.Quotient
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Subcanonical

/-!
# Affine object quotients of finite locally free groupoid schemes

This module constructs the spectrum of invariant functions of an affine finite
locally free equivalence-relation groupoid, together with its quotient morphism
over the original base scheme.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A groupoid scheme with monic `(t, s)` is an internal equivalence relation. -/
instance instIsEquivalenceRelation_of_mono {S : Scheme.{u}} (P : GroupoidScheme S)
    [Mono P.toPreRelation.hom.left] : IsEquivalenceRelation P.t P.s := sorry

/-- The arrow scheme of an affine finite locally free groupoid is affine. -/
instance instIsAffine_arrow {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] : IsAffine P.R.left := sorry

/-- The source map of a groupoid scheme makes the arrow coordinates into an algebra
over the object coordinates. -/
instance instObjectQuotientAlgebra {S : Scheme.{u}} (P : GroupoidScheme S) :
    Algebra (Γ(P.U.left, ⊤) : Type u) (Γ(P.R.left, ⊤) : Type u) :=
  (CommRingCat.Hom.hom P.s.left.appTop).toAlgebra

/-- The ring homomorphism on global sections induced by the target map. -/
def objectQuotientTargetHom {S : Scheme.{u}} (P : GroupoidScheme S) :
    (Γ(P.U.left, ⊤) : Type u) →+* (Γ(P.R.left, ⊤) : Type u) :=
  CommRingCat.Hom.hom P.t.left.appTop

/-- The target ring homomorphism is the global-sections map of `P.t`. -/
theorem objectQuotientTargetHom_eq {S : Scheme.{u}} (P : GroupoidScheme S) :
    objectQuotientTargetHom P = CommRingCat.Hom.hom P.t.left.appTop := sorry

/-- Canonical affine presentation of the object scheme. -/
def objectQuotientObjectIso {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] :
    Spec (CommRingCat.of (Γ(P.U.left, ⊤) : Type u)) ≅ P.U.left :=
  P.U.left.isoSpec.symm

/-- The object presentation is the inverse of `isoSpec`. -/
theorem objectQuotientObjectIso_eq {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] :
    objectQuotientObjectIso P = P.U.left.isoSpec.symm := sorry

/-- Canonical affine presentation of the arrow scheme. -/
def objectQuotientArrowIso {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] :
    Spec (CommRingCat.of (Γ(P.R.left, ⊤) : Type u)) ≅ P.R.left :=
  P.R.left.isoSpec.symm

/-- The arrow presentation is the inverse of `isoSpec`. -/
theorem objectQuotientArrowIso_eq {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] :
    objectQuotientArrowIso P = P.R.left.isoSpec.symm := sorry

/-- The source map is compatible with the canonical affine presentations. -/
theorem objectQuotient_source_compat {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] :
    (objectQuotientArrowIso P).hom ≫ P.s.left =
      Spec.map (CommRingCat.ofHom
          (algebraMap (Γ(P.U.left, ⊤) : Type u) (Γ(P.R.left, ⊤) : Type u))) ≫
        (objectQuotientObjectIso P).hom := sorry

/-- The target map is compatible with the canonical affine presentations. -/
theorem objectQuotient_target_compat {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] :
    (objectQuotientArrowIso P).hom ≫ P.t.left =
      Spec.map (CommRingCat.ofHom (objectQuotientTargetHom P)) ≫
        (objectQuotientObjectIso P).hom := sorry

/-- The spectrum of invariant functions of an affine finite locally free
equivalence-relation groupoid. -/
def objectQuotient {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [IsEquivalenceRelation P.t P.s] : Scheme.{u} :=
  Spec (CommRingCat.of
    ((objectQuotientTargetHom P).eqLocus
      (algebraMap (Γ(P.U.left, ⊤) : Type u) (Γ(P.R.left, ⊤) : Type u))))

/-- The object quotient is the spectrum of the invariant equalizer subring. -/
theorem objectQuotient_eq {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [IsEquivalenceRelation P.t P.s] :
    objectQuotient P =
      Spec (CommRingCat.of
        ((objectQuotientTargetHom P).eqLocus
          (algebraMap (Γ(P.U.left, ⊤) : Type u) (Γ(P.R.left, ⊤) : Type u)))) := sorry

/-- The spectrum of invariant functions is affine. -/
instance objectQuotient_isAffine {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [IsEquivalenceRelation P.t P.s] : IsAffine (objectQuotient P) := sorry

/-- The invariant spectrum of `P`, as a scheme over the original base. -/
def objectQuotientOver {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [IsEquivalenceRelation P.t P.s] : Over S :=
  invariantSpectrumOver P (objectQuotientTargetHom P) (objectQuotientObjectIso P)
    (invariantSpectrumMap_effectiveEpi P (objectQuotientTargetHom P)
      (objectQuotientObjectIso P) (objectQuotientArrowIso P)
      (objectQuotient_source_compat P) (objectQuotient_target_compat P))
    (invariantSpectrumMap_respectsBase P (objectQuotientTargetHom P)
      (objectQuotientObjectIso P) (objectQuotientArrowIso P)
      (objectQuotient_source_compat P) (objectQuotient_target_compat P))

/-- The underlying scheme of `objectQuotientOver P` is `objectQuotient P`. -/
theorem objectQuotientOver_left {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [IsEquivalenceRelation P.t P.s] :
    (objectQuotientOver P).left = objectQuotient P := sorry

/-- The canonical morphism from the object scheme to the invariant spectrum, as a
morphism over the base. -/
def objectQuotientMap {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [IsEquivalenceRelation P.t P.s] :
    P.U ⟶ objectQuotientOver P :=
  invariantSpectrumQuotientMap P (objectQuotientTargetHom P) (objectQuotientObjectIso P)
    (invariantSpectrumMap_effectiveEpi P (objectQuotientTargetHom P)
      (objectQuotientObjectIso P) (objectQuotientArrowIso P)
      (objectQuotient_source_compat P) (objectQuotient_target_compat P))
    (invariantSpectrumMap_respectsBase P (objectQuotientTargetHom P)
      (objectQuotientObjectIso P) (objectQuotientArrowIso P)
      (objectQuotient_source_compat P) (objectQuotient_target_compat P))

/-- The underlying scheme morphism of `objectQuotientMap` is the invariant-spectrum
map of the canonical presentations. -/
theorem objectQuotientMap_left {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [IsEquivalenceRelation P.t P.s] :
    (objectQuotientMap P).left =
      invariantSpectrumMap P (objectQuotientTargetHom P) (objectQuotientObjectIso P) :=
  sorry

/-- The quotient morphism equalizes the target and source maps of `P`. -/
theorem objectQuotientMap_equalizes {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [IsEquivalenceRelation P.t P.s] :
    P.toPreRelation.t ≫ objectQuotientMap P =
      P.toPreRelation.s ≫ objectQuotientMap P := sorry

/-- The quotient morphism is finite locally free. -/
instance objectQuotientMap_isFiniteLocallyFree {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [IsEquivalenceRelation P.t P.s] :
    IsFiniteLocallyFree (objectQuotientMap P).left := sorry

/-- The arrow scheme of `P` is the kernel pair of the quotient morphism. -/
instance objectQuotient_kernelPair_isIso {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [IsEquivalenceRelation P.t P.s] :
    IsIso (P.toPreRelation.kernelPairLift (objectQuotientMap P)
      (objectQuotientMap_equalizes P)) := sorry

/-- The invariant spectrum represents the fppf quotient sheaf of `P` over the base. -/
instance objectQuotient_sheaf_isIso {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [IsEquivalenceRelation P.t P.s] :
    IsIso (@Scheme.PreRelation.quotientSheafDesc _ _ _ P.toPreRelation
      (StandardTopology.fppf.overTopology S)
      (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)
      (objectQuotientMap P) (objectQuotientMap_equalizes P)) := sorry

/-- The quotient morphism of `P` viewed on an identified object scheme `G.U`. -/
def quotientMapOf {S : Scheme.{u}} {G P : GroupoidScheme S} (hU : P.U = G.U)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [IsEquivalenceRelation P.t P.s] : G.U ⟶ objectQuotientOver P :=
  eqToHom hU.symm ≫ objectQuotientMap P

/-- `quotientMapOf` is the equality-induced transport of `objectQuotientMap`. -/
theorem quotientMapOf_spec {S : Scheme.{u}} {G P : GroupoidScheme S}
    (hU : P.U = G.U) [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left]
    [IsFiniteLocallyFree P.t.left] [IsEquivalenceRelation P.t P.s] :
    quotientMapOf hU = eqToHom hU.symm ≫ objectQuotientMap P := sorry

end AlgebraicGeometry.GroupoidScheme

