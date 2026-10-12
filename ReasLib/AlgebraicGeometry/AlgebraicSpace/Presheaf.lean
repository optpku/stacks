/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RepresentableProperty
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.LocallySurjective

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A presheaf on schemes over `S` is an algebraic space if it is an fppf sheaf,
has representable diagonal, and admits a scheme atlas whose represented
pullbacks are étale and surjective. -/
def IsAlgebraicSpace {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) : Prop :=
  Presheaf.IsSheaf (Scheme.fppfTopology.over S) F ∧
    yoneda.relativelyRepresentable (Limits.diag F) ∧
      ∃ (U : Over S) (p : yoneda.obj U ⟶ F),
        Scheme.representableMorphismProperty S (@Etale ⊓ @Surjective) p

/-- A presheaf is an algebraic space exactly when it is an fppf sheaf with
representable diagonal and a representable étale atlas that is locally
surjective for the étale topology. -/
theorem isAlgebraicSpace_iff_etaleAtlas {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) :
    IsAlgebraicSpace F ↔
      Presheaf.IsSheaf (Scheme.fppfTopology.over S) F ∧
        yoneda.relativelyRepresentable (Limits.diag F) ∧
          ∃ (U : Over S) (p : yoneda.obj U ⟶ F),
            (MorphismProperty.over (@Etale)).presheaf p ∧
              Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

end AlgebraicGeometry
