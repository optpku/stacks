/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.PointDomination
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 54.4.2: a proper morphism to a Noetherian scheme that is an isomorphism away from
finitely many regular closed points of local dimension two is dominated by a finite sequence of
blowups at closed points lying above that set. -/
@[stacks 0AHI] #check (AlgebraicGeometry.Scheme.Hom.exists_pointBlowupSequence_lift :
  ∀ {X Y : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (hT_finite : T.Finite) (hT_closed : T ⊆ closedPoints X)
    (hT_regular : ∀ x, x ∈ T → IsRegularLocalRing (X.presheaf.stalk x))
    (hT_dimension : ∀ x, x ∈ T → ringKrullDim (X.presheaf.stalk x) = 2)
    (U : X.Opens) (hU : (U : Set X) = Tᶜ) (f : Y ⟶ X) [IsProper f]
    [IsIso (f ∣_ U)],
    ∃ (Xn : Scheme.{u}) (s : Scheme.PointBlowupSequence X Xn) (g : Xn ⟶ Y),
      s.EveryCenterOver T ∧ g ≫ f = s.toSource)
