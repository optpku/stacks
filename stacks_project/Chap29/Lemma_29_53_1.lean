/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Normalization
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]

#check (AlgebraicGeometry.Scheme.Hom.normalizationDiagram f : X.Opensᵒᵖ ⥤ CommRingCat)

#check (AlgebraicGeometry.Scheme.Hom.normalizationDiagramMap f :
  X.presheaf ⟶ AlgebraicGeometry.Scheme.Hom.normalizationDiagram f)

/- Lemma 29.53.1: For an affine morphism `f : Y ⟶ X` presenting a quasi-coherent
`𝒪_X`-algebra, `normalizationDiagram f` is its sectionwise integral-closure algebra. Its
coequifibered property gives quasi-coherence, identifies every stalk with the corresponding
integral closure, and identifies sections on every affine open with the corresponding integral
closure. -/
@[stacks 035F] #check
  (AlgebraicGeometry.Scheme.Hom.coequifibered_normalizationDiagramMap (f := f) :
    ((AlgebraicGeometry.Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft
      (AlgebraicGeometry.Scheme.Hom.normalizationDiagramMap f)).Coequifibered)

end AlgebraicGeometry.Scheme.Hom
