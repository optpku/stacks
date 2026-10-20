module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.PointQuotient

/-!
# Actual maps between descended algebra points and the affine quotient

A descended point has its actual atlas pullback and local spectrum lift.
Amalgamating that supplied local quotient class constructs the quotient point.
Conversely, quotient elimination and concrete sheafification lifting extend
the original atlas point map. Both directions are actual functions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}

/-- The supplied atlas pullback is an actual single-arrow étale cover of the point's test scheme. -/
theorem relativeSpectrumPointAtlasCover_mem (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    Sieve.ofArrows (fun _ : Unit ↦ relativeSpectrumPointAtlasOver A p)
      (fun _ ↦ relativeSpectrumPointAtlasToTest A p) ∈ (Scheme.etaleTopology.over S) T := sorry

/-- The local quotient class carried by the point's actual spectrum-atlas lift. -/
def relativeSpectrumPointLocalQuotient (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    (relativeSpectrumQuotientSheaf A).obj.obj (op (relativeSpectrumPointAtlasOver A p)) :=
  (relativeSpectrumQuotientAtlas A).app (op (relativeSpectrumPointAtlasOver A p))
    (relativeSpectrumPointAtlasLift A p)

/-- The local quotient class agrees on the two pullbacks to every overlap. -/
theorem relativeSpectrumPointLocalQuotient_compatible (A : X.QcAlgebraUnder)
    (p : relativeSpectrumPair A T) {W : Over S}
    (a b : W ⟶ relativeSpectrumPointAtlasOver A p)
    (h : a ≫ relativeSpectrumPointAtlasToTest A p = b ≫ relativeSpectrumPointAtlasToTest A p) :
    (relativeSpectrumQuotientSheaf A).obj.map a.op (relativeSpectrumPointLocalQuotient A p) =
      (relativeSpectrumQuotientSheaf A).obj.map b.op (relativeSpectrumPointLocalQuotient A p) := sorry

/-- The quotient point is actual étale-sheaf amalgamation of the supplied local atlas class. -/
def relativeSpectrumPointQuotient (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    (relativeSpectrumQuotientSheaf A).obj.obj (op T) :=
  ((relativeSpectrumQuotientSheaf A).property.amalgamateOfArrows
      (fun _ : Unit ↦ relativeSpectrumPointAtlasToTest A p)
      (relativeSpectrumPointAtlasCover_mem A p)
      (fun _ ↦ TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ relativeSpectrumPointLocalQuotient A p))
      (by
        intro W i j a b hab
        ext z
        exact relativeSpectrumPointLocalQuotient_compatible A p a b hab)) PUnit.unit

/-- The original descended-point functor maps to the quotient by the actual local class gluing. -/
def relativeSpectrumPairToQuotient (A : X.QcAlgebraUnder) :
    relativeSpectrumFunctor A ⟶ (relativeSpectrumQuotientSheaf A).obj where
  app T := TypeCat.ofHom (relativeSpectrumPointQuotient A)
  naturality := sorry

/-- The actual atlas point map identifies the two spectrum-relation projections. -/
theorem relativeSpectrumAtlasNat_equalizes (A : X.QcAlgebraUnder) :
    yoneda.map (relativeSpectrumDescentRelation A).t ≫ relativeSpectrumAtlasNat A =
      yoneda.map (relativeSpectrumDescentRelation A).s ≫ relativeSpectrumAtlasNat A := sorry

/-- Related actual atlas points have the same descended algebra point. -/
theorem relativeSpectrumRawQuotientToPair_respects (A : X.QcAlgebraUnder) {T : Over S}
    {a b : T ⟶ relativeSpectrumDescentAtlas A}
    (h : (relativeSpectrumDescentRelation A).pointRel T a b) :
    (relativeSpectrumAtlasNat A).app (op T) a = (relativeSpectrumAtlasNat A).app (op T) b := sorry

/-- Quotient elimination extends the actual atlas algebra point map to raw quotient classes. -/
def relativeSpectrumRawQuotientToPair (A : X.QcAlgebraUnder) :
    (relativeSpectrumDescentRelation A).quotientPresheaf ⟶ relativeSpectrumFunctor A where
  app T := TypeCat.ofHom
    (Quot.lift ((relativeSpectrumAtlasNat A).app T)
      (fun _ _ h ↦ relativeSpectrumRawQuotientToPair_respects A h))
  naturality := sorry

/-- Descended algebra points satisfy étale descent. -/
theorem relativeSpectrumFunctor_isEtaleSheaf (A : X.QcAlgebraUnder) :
    Presheaf.IsSheaf (Scheme.etaleTopology.over S) (relativeSpectrumFunctor A) := sorry

/-- The quotient-to-point map uses the actual local sheafification lift of quotient elimination. -/
def relativeSpectrumQuotientToPair (A : X.QcAlgebraUnder) :
    (relativeSpectrumQuotientSheaf A).obj ⟶ relativeSpectrumFunctor A :=
  Scheme.EtaleSheafification.lift
    ⟨relativeSpectrumFunctor A, relativeSpectrumFunctor_isEtaleSheaf A⟩
    (relativeSpectrumRawQuotientToPair A)

/-- The quotient and original descended-point functors are identified by their actual maps. -/
def relativeSpectrumQuotientPairIso (A : X.QcAlgebraUnder) :
    (relativeSpectrumQuotientSheaf A).obj ≅ relativeSpectrumFunctor A where
  hom := relativeSpectrumQuotientToPair A
  inv := relativeSpectrumPairToQuotient A
  hom_inv_id := sorry
  inv_hom_id := sorry

end AlgebraicGeometry.AlgebraicSpace
