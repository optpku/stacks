/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.Monoidal.Functor.TensorComparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Internal Hom across a monoidal adjunction

@stack 0E1W

For a monoidal adjunction `L ⊣ R`, the two functors
`R ⋙ Hom_C(K, -)` and `Hom_D(L K, -) ⋙ R` are right adjoint to naturally
isomorphic fixed-left tensor functors.  This file packages the resulting
relative internal-Hom comparison without choosing a new internal-Hom object.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

noncomputable section

universe uC vC uD vD

namespace CategoryTheory.Adjunction.InternalHom

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
variable {L : C ⥤ D} {R : D ⥤ C}

/-- Naturality of the fixed-left component of a tensor comparison. -/
@[stacks 0E1W "fixed-left tensor comparison naturality"]
theorem tensorLeftComparison_naturality
    (T : Functor.TensorComparison L) (K : C) :
    ∀ {X Y : C} (f : X ⟶ Y),
      L.map ((tensorLeft K).map f) ≫ T.hom.app (K, Y) =
        T.hom.app (K, X) ≫ (tensorLeft (L.obj K)).map (L.map f) := sorry

/-- A tensor comparison identifies the two fixed-left tensor functors associated
to a functor.  Its components are the supplied tensor-comparison components. -/
@[stacks 0E1W "fixed-left tensor functor comparison"]
noncomputable def tensorLeftComparison
    (T : Functor.TensorComparison L) (K : C) :
    tensorLeft K ⋙ L ≅ L ⋙ tensorLeft (L.obj K) :=
  NatIso.ofComponents (fun X => T.app (K, X))
    (fun {_ _} f => tensorLeftComparison_naturality T K f)

/-- The composite adjunction with right adjoint `R ⋙ Hom_C(K, -)`. -/
@[stacks 0E1W "source relative internal-Hom adjunction"]
noncomputable def sourceAdjunction (adj : L ⊣ R) (H : MonoidalClosed C) (K : C) :
    tensorLeft K ⋙ L ⊣ R ⋙ MonoidalClosed.ihomOf H K :=
  (MonoidalClosed.adjunctionOf H K).comp adj

/-- The composite adjunction with right adjoint `Hom_D(L K, -) ⋙ R`. -/
@[stacks 0E1W "target relative internal-Hom adjunction"]
noncomputable def targetAdjunction (adj : L ⊣ R) (H : MonoidalClosed D) (K : C) :
    L ⋙ tensorLeft (L.obj K) ⊣ MonoidalClosed.ihomOf H (L.obj K) ⋙ R :=
  adj.comp (MonoidalClosed.adjunctionOf H (L.obj K))

/-- The natural relative internal-Hom isomorphism determined by an explicit
monoidal adjunction, two closed owners, and a tensor comparison for its left adjoint. -/
@[stacks 0E1W "relative internal-Hom natural isomorphism"]
noncomputable def comparisonNatIso
    (adj : L ⊣ R) (HC : MonoidalClosed C) (HD : MonoidalClosed D)
    (T : Functor.TensorComparison L) (K : C) :
    R ⋙ MonoidalClosed.ihomOf HC K ≅
      MonoidalClosed.ihomOf HD (L.obj K) ⋙ R :=
  ((sourceAdjunction adj HC K).ofNatIsoLeft (tensorLeftComparison T K)).rightAdjointUniq
    (targetAdjunction adj HD K)

/-- The objectwise relative internal-Hom isomorphism. -/
@[stacks 0E1W "relative internal-Hom object isomorphism"]
noncomputable def comparisonIso
    (adj : L ⊣ R) (HC : MonoidalClosed C) (HD : MonoidalClosed D)
    (T : Functor.TensorComparison L) (K : C) (M : D) :
    (MonoidalClosed.ihomOf HC K).obj (R.obj M) ≅
      R.obj ((MonoidalClosed.ihomOf HD (L.obj K)).obj M) :=
  (comparisonNatIso adj HC HD T K).app M

end CategoryTheory.Adjunction.InternalHom
