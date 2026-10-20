/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.AtlasMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Functor

/-!
# The concrete atlas point in the original relative-spectrum functor

The constructed scheme and its actual global algebra map give a point in the
original descended atlas encoding. Yoneda turns this supplied point into the
atlas natural transformation, preserving the original functor of points.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The original relative-spectrum point carried by the actual constructed atlas scheme. -/
def relativeSpectrumAtlasPoint (A : X.QcAlgebraUnder) :
    relativeSpectrumPair A (relativeSpectrumDescentAtlas A) :=
  relativeSpectrumPairMk (relativeSpectrumDescentAtlasHomToX A) (relativeSpectrumAtlasAlgebraMap A)

/-- The actual atlas transformation into the original relative-spectrum functor of points. -/
def relativeSpectrumAtlasNat (A : X.QcAlgebraUnder) :
    yoneda.obj (relativeSpectrumDescentAtlas A) ⟶ relativeSpectrumFunctor A :=
  yonedaEquiv.symm (relativeSpectrumAtlasPoint A)

/-- The atlas transformation is determined by the supplied original relative-spectrum point. -/
theorem relativeSpectrumAtlasNat_yoneda (A : X.QcAlgebraUnder) :
    yonedaEquiv (relativeSpectrumAtlasNat A) = relativeSpectrumAtlasPoint A :=
  Equiv.apply_symm_apply yonedaEquiv _

/-- The actual atlas's base point is the supplied structural morphism through the stored base atlas. -/
theorem relativeSpectrumAtlasPoint_base (A : X.QcAlgebraUnder) :
    (relativeSpectrumAtlasPoint A).1 =
      yonedaEquiv (relativeSpectrumDescentAtlasToX A) := rfl

end AlgebraicGeometry.AlgebraicSpace
