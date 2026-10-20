module

public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.Limits.IsLimit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct.Cocone
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.CartesianSystem
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SeparatedOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-! # Colimits of algebraic spaces separated over a base -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u v
namespace AlgebraicGeometry.AlgebraicSpace
variable {J : Type v} [Category.{v} J] {S : Scheme.{u}} {B : AlgebraicSpace S}
variable {D : J ⥤ Over B}

/-- A cartesian étale system descends from the separated étale site of a cocone apex. -/
def IsInSeparatedSpacesEtaleEssImage (c : Cocone D)
    (sys : CartesianSpacesEtaleSystem D) : Prop :=
  ∃ (U : spacesEtaleSite c.pt.left), Separated U.hom ∧
    ∃ (e : sys.functor ≅ (ofSpacesEtalePullback c U).functor),
      sys.π = e.hom ≫ (ofSpacesEtalePullback c U).π

/-- Separated étale essential-image membership is the pullback-system specification. -/
theorem isInSeparatedSpacesEtaleEssImage_iff (c : Cocone D)
    (sys : CartesianSpacesEtaleSystem D) :
    IsInSeparatedSpacesEtaleEssImage c sys ↔
      ∃ (U : spacesEtaleSite c.pt.left), Separated U.hom ∧
        ∃ (e : sys.functor ≅ (ofSpacesEtalePullback c U).functor),
          sys.π = e.hom ≫ (ofSpacesEtalePullback c U).π := sorry

/-- A separated-over colimit is a colimit in `Over B` under the coproduct, base-change, and
essential-image hypotheses. -/
theorem isColimit_of_separatedOver [Small.{u} J]
    (D : J ⥤ Over B) (c : Cocone D)
    (h_sep : ∀ i, Separated (D.obj i).hom) (h_pt : Separated c.pt.hom)
    (h_colim : IsColimitAmongSeparated c)
    (h_surj : Surjective (coproductToColimit c))
    (h_etale_colim : ∀ {U : AlgebraicSpace S} (f : U ⟶ c.pt.left) [Etale f] [Separated f],
      IsColimitAmongSeparated (baseChangeCocone c f))
    (h_ess : ∀ sys : CartesianSpacesEtaleSystem D,
      (∀ i, Separated (sys.π.app i)) → IsInSeparatedSpacesEtaleEssImage c sys) :
    Nonempty (IsColimit c) := sorry
end AlgebraicGeometry.AlgebraicSpace
