module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Covering
public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardSyntomic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Smooth

/-!
# Syntomic covers in chosen big-site presentations

Syntomic and Zariski covering families of the scheme underlying an object in a
chosen big syntomic site can be represented by covering families in the chosen
carrier.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigSite

variable (X : ChosenBigSite.{u, v} (Scheme.precoverage (@Syntomic))) (T : X.carrier)

/-- Every syntomic cover of the underlying scheme of a chosen-site object is
refined by the image of a covering family in the chosen carrier. -/
theorem exists_coveringFamily_refining_syntomicCover
    (𝒰 : SyntomicCover.{u, u} (X.toScheme.obj T)) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
      Limits.FormalCoproduct.Over.IsCovering
          (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
            X.hasPullbacks X.pretopology) 𝒱 ∧
        Nonempty
          (((Limits.FormalCoproduct.map (Over.post (X := T) X.toScheme)).obj 𝒱) ⟶
            Limits.FormalCoproduct.Over.ofArrows 𝒰.X 𝒰.f) := sorry

/-- Every standard syntomic cover of the underlying affine scheme of a chosen-site
object is tautologically equivalent to the image of a covering family in the
chosen carrier. -/
theorem exists_coveringFamily_tautologicallyEquivalent_standardSyntomicCovering
    [IsAffine (X.toScheme.obj T)]
    (𝒰 : StandardSyntomicCovering (X.toScheme.obj T)) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
      Limits.FormalCoproduct.Over.IsCovering
          (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
            X.hasPullbacks X.pretopology) 𝒱 ∧
        Limits.FormalCoproduct.TautologicallyEquivalent
          (Limits.FormalCoproduct.Over.ofArrows
            (fun j : ULift.{u} (Fin 𝒰.n) ↦ 𝒰.U j.down)
            (fun j : ULift.{u} (Fin 𝒰.n) ↦ 𝒰.map j.down))
          ((Limits.FormalCoproduct.map (Over.post (X := T) X.toScheme)).obj 𝒱) := sorry

/-- Every Zariski open cover of the underlying scheme of a chosen-site object is
tautologically equivalent to the image of a covering family in the chosen
syntomic carrier. -/
theorem exists_coveringFamily_tautologicallyEquivalent_zariskiCover
    (𝒰 : (X.toScheme.obj T).OpenCover.{u}) :
    ∃ 𝒱 : Limits.FormalCoproduct.{u} (Over T),
      Limits.FormalCoproduct.Over.IsCovering
          (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier)
            X.hasPullbacks X.pretopology) 𝒱 ∧
        Limits.FormalCoproduct.TautologicallyEquivalent
          (Limits.FormalCoproduct.Over.ofArrows 𝒰.X 𝒰.f)
          ((Limits.FormalCoproduct.map (Over.post (X := T) X.toScheme)).obj 𝒱) := sorry

end AlgebraicGeometry.ChosenBigSite
