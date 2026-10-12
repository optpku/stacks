/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Normalization
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]

/- Definition 29.53.2: For a quasi-coherent `𝒪_X`-algebra represented by an affine
morphism `f : Y ⟶ X`, the integral closure of `𝒪_X` in that algebra is the canonical
presheaf `normalizationDiagram f`. -/
@[stacks 035G] #check (AlgebraicGeometry.Scheme.Hom.normalizationDiagram f :
  X.Opensᵒᵖ ⥤ CommRingCat)

end AlgebraicGeometry.Scheme.Hom
