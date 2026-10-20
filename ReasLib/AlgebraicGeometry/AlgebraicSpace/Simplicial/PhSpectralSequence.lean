module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.Cohomology
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment
public import ReasLib.CategoryTheory.Sites.Hypercovering.Augmented
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.Site

/-!
# Étale cohomology spectral sequences for ph hypercoverings

An augmented simplicial algebraic space that is a ph hypercovering gives a
convergent spectral sequence from the étale cohomology of its stages to that
of its augmentation target. The spectral sequences have simultaneous choices
that are functorial in arbitrary abelian coefficient sheaves.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Functor FilteredComplex.SpectralSequence.Realization
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- For a ph hypercovering of an algebraic space, the étale cohomology spectral
sequences can be chosen simultaneously for all abelian sheaves, with natural
first-page comparisons and maps preserving identities and composition. -/
theorem spectralSequence_functorial
    (ha : (SimplicialObject.Augmentation.toAugmented a).IsHypercovering (phTopology S)) :
    ∃ (E : ∀ F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1},
        WithAbutment (fun n ↦ plusCohomology X n) F)
      (e : ∀ (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) (p q : ℤ),
        ((E F).sequence.page 1).X (p, q) ≅ (pageOneFunctor a p q).obj F)
      (m : ∀ {F G : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}} (f : F ⟶ G),
        WithAbutment.Map (fun n ↦ plusCohomology X n) f (E F) (E G)),
      (∀ {F G : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}} (f : F ⟶ G) (p q : ℤ),
        ((m f).sequenceMap.hom 1).f (p, q) ≫ (e G p q).hom =
          (e F p q).hom ≫ (pageOneFunctor a p q).map f) ∧
      (∀ F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1},
        (m (𝟙 F)).sequenceMap = 𝟙 (E F).sequence) ∧
      (∀ {F G H : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}}
          (f : F ⟶ G) (g : G ⟶ H),
        (m (f ≫ g)).sequenceMap = (m f).sequenceMap ≫ (m g).sequenceMap) := sorry

/-- A ph hypercovering of an algebraic space yields a convergent cohomological
spectral sequence for every abelian étale sheaf, with first page given by the
étale cohomology of the stage pullbacks and abutment given by the étale
cohomology of the augmentation target. -/
theorem exists_spectralSequence
    (ha : (SimplicialObject.Augmentation.toAugmented a).IsHypercovering (phTopology S))
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :
    ∃ E : WithAbutment (fun n ↦ plusCohomology X n) F,
      Nonempty (∀ p q : ℤ,
        (E.sequence.page 1).X (p, q) ≅ (pageOneFunctor a p q).obj F) := sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
