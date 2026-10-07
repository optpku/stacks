module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation

/-!
# Realizing covers in chosen big-site presentations

Ambient covers of schemes can be represented by covering families in a chosen
big site, up to componentwise isomorphism in the corresponding slice category.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigSite

variable {P : Precoverage Scheme.{u}}

/-- Every ambient cover of the scheme underlying an object in a chosen big site is
tautologically equivalent to the image of a covering family in the chosen carrier. -/
theorem exists_coveringFamily_tautologicallyEquivalent
    (X : ChosenBigSite.{u, v} P) {T : X.carrier}
    (𝒰 : Scheme.Cover.{u} P (X.toScheme.obj T)) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (CategoryTheory.Over T),
      Limits.FormalCoproduct.Over.IsCovering
          (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
            X.hasPullbacks X.pretopology) 𝒱 ∧
        Limits.FormalCoproduct.TautologicallyEquivalent
          ((Limits.FormalCoproduct.map
            (CategoryTheory.Over.post (X := T) X.toScheme)).obj 𝒱)
          (Limits.FormalCoproduct.Over.ofArrows 𝒰.X 𝒰.f) := sorry

/-- Every ambient cover of the scheme underlying an object in a chosen big site is
refined by the image of a covering family in the chosen carrier. -/
theorem exists_coveringFamily_refining
    (X : ChosenBigSite.{u, v} P) {T : X.carrier}
    (𝒰 : Scheme.Cover.{u} P (X.toScheme.obj T)) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (CategoryTheory.Over T),
      Limits.FormalCoproduct.Over.IsCovering
          (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
            X.hasPullbacks X.pretopology) 𝒱 ∧
        Nonempty
          (((Limits.FormalCoproduct.map
            (CategoryTheory.Over.post (X := T) X.toScheme)).obj 𝒱) ⟶
            Limits.FormalCoproduct.Over.ofArrows 𝒰.X 𝒰.f) := sorry

end AlgebraicGeometry.ChosenBigSite
