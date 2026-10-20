module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantSpectrum.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Representability
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Subcanonical

/-!
# Affine quotients of finite locally free groupoid schemes

The spectrum of invariant global functions carries the canonical quotient map and
represents the fppf quotient of an affine finite locally free equivalence relation.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A groupoid scheme with monic `(t, s)` is an internal equivalence relation. -/
theorem isEquivalenceRelation_of_mono {S : Scheme.{u}} (P : GroupoidScheme S)
    [Mono P.toPreRelation.hom.left] : IsEquivalenceRelation P.t P.s := sorry

/-- The ring homomorphism on global sections induced by the target map. -/
def objectQuotientTargetHom {S : Scheme.{u}} (P : GroupoidScheme S) :
    (Γ(P.U.left, ⊤) : Type u) →+* (Γ(P.R.left, ⊤) : Type u) :=
  CommRingCat.Hom.hom P.t.left.appTop

/-- The spectrum of global functions equalized by the target and source maps. -/
def objectQuotient {S : Scheme.{u}} (P : GroupoidScheme S) : Scheme.{u} :=
  Spec (CommRingCat.of ((objectQuotientTargetHom P).eqLocus
    (CommRingCat.Hom.hom P.s.left.appTop)))

/-- The object quotient is the spectrum of the invariant equalizer subring. -/
theorem objectQuotient_eq {S : Scheme.{u}} (P : GroupoidScheme S) :
    objectQuotient P = Spec (CommRingCat.of ((objectQuotientTargetHom P).eqLocus
      (CommRingCat.Hom.hom P.s.left.appTop))) := sorry

/-- The canonical projection to the spectrum of invariant global functions. -/
def objectQuotientProjection {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] : P.U.left ⟶ objectQuotient P :=
  P.U.left.isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom ((objectQuotientTargetHom P).eqLocus
      (CommRingCat.Hom.hom P.s.left.appTop)).subtype)

/-- The structure morphism to the base is constant on the fibres of the canonical
invariant-spectrum projection. -/
theorem objectQuotientProjection_respectsBase {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] :
    ∀ {T : Scheme.{u}} (f g : T ⟶ P.U.left),
      f ≫ objectQuotientProjection P = g ≫ objectQuotientProjection P →
        f ≫ P.U.hom = g ≫ P.U.hom := sorry

/-- The canonical invariant-spectrum projection of an affine finite locally free
equivalence-relation groupoid is an effective epimorphism. -/
theorem objectQuotientProjection_effectiveEpi {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] : EffectiveEpi (objectQuotientProjection P) :=
  let sourceAlgebra := (CommRingCat.Hom.hom P.s.left.appTop).toAlgebra
  let objectPresentation := P.U.left.isoSpec.symm
  let arrowAffine := isAffine_of_isAffineHom P.s.left
  let arrowPresentation := (@Scheme.isoSpec P.R.left arrowAffine).symm
  let sourceCompatibility :=
    (@Scheme.isoSpec_inv_naturality _ _ arrowAffine inferInstance P.s.left).symm
  let targetCompatibility :=
    (@Scheme.isoSpec_inv_naturality _ _ arrowAffine inferInstance P.t.left).symm
  let finiteLocallyFree := @invariantSpectrumMap_isFiniteLocallyFree _ P _ _ _ _ sourceAlgebra
    (objectQuotientTargetHom P) objectPresentation arrowPresentation
    sourceCompatibility targetCompatibility inferInstance inferInstance
    (isEquivalenceRelation_of_mono P)
  let surjective := @invariantSpectrumMap_surjective _ P _ _ _ _ sourceAlgebra
    (objectQuotientTargetHom P) objectPresentation arrowPresentation
    sourceCompatibility targetCompatibility inferInstance inferInstance
  (isRegularEpi_iff_effectiveEpi (objectQuotientProjection P)).mp
    (@isRegularEpi_of_flat_of_surjective_of_isAffine _ _ inferInstance (isAffine_Spec _)
      (objectQuotientProjection P) ⟨surjective⟩ finiteLocallyFree.flat)

/-- The invariant spectrum, equipped with its descended morphism to the base scheme. -/
def objectQuotientOver {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] : Over S :=
  Over.mk (@EffectiveEpi.desc _ _ _ _ _ (objectQuotientProjection P)
    (objectQuotientProjection_effectiveEpi P) P.U.hom
    (objectQuotientProjection_respectsBase P))

/-- The underlying scheme of the quotient over the base is the invariant spectrum. -/
theorem objectQuotientOver_left {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] :
    (objectQuotientOver P).left = objectQuotient P := sorry

/-- The canonical invariant-spectrum quotient morphism over the base scheme. -/
def objectQuotientMap {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] : P.U ⟶ objectQuotientOver P :=
  Over.homMk (objectQuotientProjection P)
    (@EffectiveEpi.fac _ _ _ _ _ (objectQuotientProjection P)
      (objectQuotientProjection_effectiveEpi P) P.U.hom
      (objectQuotientProjection_respectsBase P))

/-- The underlying quotient morphism is the spectrum map of the invariant-ring inclusion,
transported through the canonical affine presentation of the object scheme. -/
theorem objectQuotientMap_left {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] :
    (objectQuotientMap P).left = P.U.left.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom ((objectQuotientTargetHom P).eqLocus
        (CommRingCat.Hom.hom P.s.left.appTop)).subtype) := sorry

/-- The quotient morphism equalizes the target and source maps. -/
theorem objectQuotientMap_equalizes {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] :
    P.toPreRelation.t ≫ objectQuotientMap P =
      P.toPreRelation.s ≫ objectQuotientMap P := sorry

/-- The canonical comparison from the fppf quotient sheaf to the represented
invariant spectrum over the base scheme. -/
def objectQuotientSheafComparison {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] :=
  @Scheme.PreRelation.quotientSheafDesc _ _ _ P.toPreRelation
    (StandardTopology.fppf.overTopology S)
    (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)
    (objectQuotientMap P) (objectQuotientMap_equalizes P)

/-- The quotient morphism is finite locally free. -/
theorem objectQuotientMap_isFiniteLocallyFree {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] :
    IsFiniteLocallyFree (objectQuotientMap P).left := sorry

/-- The canonical `(t, s)` comparison identifies the arrow scheme with the kernel
pair of the quotient morphism. -/
theorem objectQuotient_kernelPair_isIso {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] :
    IsIso (P.toPreRelation.kernelPairLift (objectQuotientMap P)
      (objectQuotientMap_equalizes P)) := sorry

/-- The quotient morphism transported to an identified object scheme. -/
def quotientMapOf {S : Scheme.{u}} {G P : GroupoidScheme S} (hU : P.U = G.U)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] : G.U ⟶ objectQuotientOver P :=
  eqToHom hU.symm ≫ objectQuotientMap P

/-- The transported quotient morphism is the composite of the equality-induced
identification and the canonical quotient morphism. -/
theorem quotientMapOf_spec {S : Scheme.{u}} {G P : GroupoidScheme S}
    (hU : P.U = G.U) [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left]
    [IsFiniteLocallyFree P.t.left] [Mono P.toPreRelation.hom.left] :
    quotientMapOf hU = eqToHom hU.symm ≫ objectQuotientMap P := sorry

/-- The invariant spectrum is affine and represents the fppf quotient sheaf. -/
theorem objectQuotient_represents {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] :
    IsAffine (objectQuotient P) ∧ IsIso (objectQuotientSheafComparison P) := sorry

/-- Equality-induced transport of the quotient morphism preserves finite local freeness. -/
theorem quotientMapOf_isFiniteLocallyFree {S : Scheme.{u}} {G P : GroupoidScheme S}
    (hU : P.U = G.U) [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left]
    [IsFiniteLocallyFree P.t.left] [Mono P.toPreRelation.hom.left] :
    IsFiniteLocallyFree (quotientMapOf hU).left := sorry

end AlgebraicGeometry.GroupoidScheme
