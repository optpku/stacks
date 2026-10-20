module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZeroComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProperSupport
public import Mathlib.CategoryTheory.Subfunctor.Image

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [IsSeparated j]

variable
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]

variable (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})

/-- For a separated étale morphism, the image of the canonical comparison from
abelian extension by zero to direct image is the subfunctor of sections whose
supports are proper over the étale base object. -/
theorem abelianExtensionByZeroToDirectImage_range_eq :
    Subfunctor.range
      (Functor.whiskerRight
        ((AlgebraicGeometry.Scheme.abelianExtensionByZeroToDirectImage j).app F).hom
        (CategoryTheory.forget AddCommGrpCat)) =
      properSupportSubfunctor j F :=
  sorry

/-- A section of an abelian direct image along a separated étale morphism lifts
to extension by zero if and only if its support is proper over the étale base object. -/
theorem mem_range_abelianExtensionByZeroToDirectImage_iff
    (V : X.Etale) (σ : F.obj.obj (op ((smallEtalePullback j).obj V))) :
    (∃ τ,
      ((AlgebraicGeometry.Scheme.abelianExtensionByZeroToDirectImage j).app F).hom.app
        (op V) τ = σ) ↔
      HasProperSupport j F V σ :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
