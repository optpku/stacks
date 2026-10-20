/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.FormalGlueing

/-!
# Formal glueing of quasi-coherent modules

The category `QCoh(Y → X, Z)` of triples `(H, G, φ)` is the categorical pullback of
quasi-coherent pullback along `f|_V : V ⟶ U` and along `j' : V ⟶ Y`. The canonical
functor `QCoh X ⥤ QCoh(Y → X, Z)` sends `F` to `(F|_U, f^* F, can)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.ObjectProperty
open CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing

/-- Pullback along a composite identifies with successive quasi-coherent pullbacks. -/
def pullbackCompIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  (AlgebraicGeometry.AlgebraicSpace.QCoh.pullbackCompIso g f).symm

/-- The restriction `f|_V : V ⟶ U` of `f : Y ⟶ X` to the open complements of `Z` and
`f⁻¹Z`. -/
abbrev restrict {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] :
    closedImmersionComplement (inverseImageι f i) ⟶ closedImmersionComplement i :=
  restrictToComplement f i

/-- The square with vertices `V`, `Y`, `U`, `X` commutes: `restrict ≫ j = j' ≫ f`. -/
theorem restrict_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] :
    restrict f i ≫ closedImmersionComplementι i =
      closedImmersionComplementι (inverseImageι f i) ≫ f :=
  restrictToComplement_comp f i

end AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing
