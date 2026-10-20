/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Descent
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Sheafification.Lift

/-!
# The actual relative-spectrum quotient and its map to the base

The quotient is the Type-u étale sheafification of the constructed affine
descent relation. Its projection to X is obtained from the actual atlas map by
quotient elimination followed by concrete étale sheafification lifting.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The actual map from the constructed affine atlas to the original algebraic space. -/
def relativeSpectrumDescentAtlasToX (A : X.QcAlgebraUnder) :
    yoneda.obj (relativeSpectrumDescentAtlas A) ⟶ X.functorOfPoints :=
  yoneda.map (Over.homMk
    (Scheme.relativeSpectrumOver
      (QcAlgebraUnder.onChart A (relativeSpectrumAtlasChart X))).π rfl) ≫ atlasHom X

/-- The two actual affine relation projections have the same image in X. -/
theorem relativeSpectrumDescentAtlasToX_equalizes (A : X.QcAlgebraUnder) :
    yoneda.map (relativeSpectrumDescentRelation A).t ≫ relativeSpectrumDescentAtlasToX A =
      yoneda.map (relativeSpectrumDescentRelation A).s ≫ relativeSpectrumDescentAtlasToX A := sorry

/-- A relation pair has equal images under the atlas structural map. -/
theorem relativeSpectrumQuotientToX_respects (A : X.QcAlgebraUnder) {T : Over S}
    {a b : T ⟶ relativeSpectrumDescentAtlas A}
    (h : (relativeSpectrumDescentRelation A).pointRel T a b) :
    (relativeSpectrumDescentAtlasToX A).app (op T) a =
      (relativeSpectrumDescentAtlasToX A).app (op T) b := sorry

/-- The structural map on raw quotient classes, induced by the actual atlas structural map. -/
def relativeSpectrumQuotientPresheafToX (A : X.QcAlgebraUnder) :
    (relativeSpectrumDescentRelation A).quotientPresheaf ⟶ X.functorOfPoints where
  app T := TypeCat.ofHom
    (Quot.lift ((relativeSpectrumDescentAtlasToX A).app T)
      (fun _ _ h ↦ relativeSpectrumQuotientToX_respects A h))
  naturality := sorry

/-- The original algebraic space's functor of points is an étale sheaf. -/
theorem relativeSpectrumBase_isEtaleSheaf (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.etaleTopology.over S) X.functorOfPoints := sorry

/-- The actual quotient sheaf of the affine spectrum descent relation. -/
abbrev relativeSpectrumQuotientSheaf (A : X.QcAlgebraUnder) :
    Sheaf (Scheme.etaleTopology.over S) (Type u) :=
  (relativeSpectrumDescentRelation A).smallEtaleQuotientSheaf

/-- Extend the raw quotient structural map using actual local sheafification lifts. -/
def relativeSpectrumQuotientToX (A : X.QcAlgebraUnder) :
    (relativeSpectrumQuotientSheaf A).obj ⟶ X.functorOfPoints :=
  Scheme.EtaleSheafification.lift
    ⟨X.functorOfPoints, relativeSpectrumBase_isEtaleSheaf X⟩
    (relativeSpectrumQuotientPresheafToX A)

/-- The quotient atlas map is the actual quotient-class projection followed by sheafification. -/
def relativeSpectrumQuotientAtlas (A : X.QcAlgebraUnder) :
    yoneda.obj (relativeSpectrumDescentAtlas A) ⟶ (relativeSpectrumQuotientSheaf A).obj :=
  (relativeSpectrumDescentRelation A).smallEtaleQuotientSheafMk

/-- The quotient atlas's structural composite is the actual map through the base atlas. -/
theorem relativeSpectrumQuotientAtlas_toX (A : X.QcAlgebraUnder) :
    relativeSpectrumQuotientAtlas A ≫ relativeSpectrumQuotientToX A =
      relativeSpectrumDescentAtlasToX A := sorry

end AlgebraicGeometry.AlgebraicSpace
