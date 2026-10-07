module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Covering

/-!
# Covering families in chosen big `ph` sites

Displayed `ph`, standard `ph`, and Zariski covering families can be compared
with covering families in an explicit chosen big `ph` presentation.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigPhSite

variable (Schph : ChosenBigPhSite.{u, v}) {T : Schph.carrier}

/-- Every `ph` covering of the scheme underlying an object in a chosen big
`ph` site is refined by a covering family in the chosen carrier. -/
theorem exists_coveringFamily_refining_phCovering
    {ι : Type u} (X : ι → Scheme.{u}) (π : ∀ i, X i ⟶ Schph.toScheme.obj T)
    (hπ : PhCovering X π) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
      Limits.FormalCoproduct.Over.IsCovering
          (@Pretopology.toPrecoverage Schph.carrier (Cat.str Schph.carrier)
            Schph.hasPullbacks Schph.pretopology) 𝒱 ∧
        Nonempty
          (((Limits.FormalCoproduct.map
            (Over.post (X := T) Schph.toScheme)).obj 𝒱) ⟶
            Limits.FormalCoproduct.Over.ofArrows X π) := sorry

/-- Every standard `ph` covering of the affine scheme underlying an object in
a chosen big `ph` site is tautologically equivalent to a covering family in
the chosen carrier. -/
theorem exists_coveringFamily_tautologicallyEquivalent_standardPhCovering
    [IsAffine (Schph.toScheme.obj T)] (𝒰₀ : StandardPhCovering (Schph.toScheme.obj T)) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
      Limits.FormalCoproduct.Over.IsCovering
          (@Pretopology.toPrecoverage Schph.carrier (Cat.str Schph.carrier)
            Schph.hasPullbacks Schph.pretopology) 𝒱 ∧
        Limits.FormalCoproduct.TautologicallyEquivalent
          (Limits.FormalCoproduct.Over.ofArrows
            (fun j : ULift.{u} (Fin 𝒰₀.m) ↦ 𝒰₀.obj j.down)
            (fun j : ULift.{u} (Fin 𝒰₀.m) ↦ 𝒰₀.map j.down))
          ((Limits.FormalCoproduct.map
            (Over.post (X := T) Schph.toScheme)).obj 𝒱) := sorry

/-- Every Zariski open covering of the scheme underlying an object in a chosen
big `ph` site is tautologically equivalent to a covering family in the chosen
carrier. -/
theorem exists_coveringFamily_tautologicallyEquivalent_zariskiCover
    (𝒰₀ : (Schph.toScheme.obj T).OpenCover.{u}) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
      Limits.FormalCoproduct.Over.IsCovering
          (@Pretopology.toPrecoverage Schph.carrier (Cat.str Schph.carrier)
            Schph.hasPullbacks Schph.pretopology) 𝒱 ∧
        Limits.FormalCoproduct.TautologicallyEquivalent
          (Limits.FormalCoproduct.Over.ofArrows 𝒰₀.X 𝒰₀.f)
          ((Limits.FormalCoproduct.map
            (Over.post (X := T) Schph.toScheme)).obj 𝒱) := sorry

end AlgebraicGeometry.ChosenBigPhSite
