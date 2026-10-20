module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SpaceOfSections.Surjective
import StacksCheckRecall

/-!
# Étale-local sections of a surjective étale morphism onto a finite scheme
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 97.9.1: A surjective étale morphism onto a finite scheme admits a
section after a surjective étale base change of the base scheme. -/
@[stacks 05XQ] #check (AlgebraicGeometry.AlgebraicSpace.exists_surjective_etale_baseChange_section :
  ∀ {U Z : Scheme.{u}} (π : Z ⟶ U) [IsFinite π] {W : AlgebraicSpace U}
    (f : W ⟶ ofOver (Over.mk π)) [Etale f] [Surjective f],
    ∃ (U' : Scheme.{u}) (g : U' ⟶ U),
      AlgebraicGeometry.Etale g ∧ AlgebraicGeometry.Surjective g ∧
        ∃ (σ : baseChange g (ofOver (Over.mk π)) ⟶ baseChange g W),
          σ ≫ baseChangeMap g f = 𝟙 (baseChange g (ofOver (Over.mk π))))

#check (AlgebraicGeometry.AlgebraicSpace.exists_surjective_etale_baseChange_section_iff_isSplitEpi :
  ∀ {U Z : Scheme.{u}} (π : Z ⟶ U) [IsFinite π] {W : AlgebraicSpace U}
    (f : W ⟶ ofOver (Over.mk π)) [Etale f] [Surjective f],
    (∃ (U' : Scheme.{u}) (g : U' ⟶ U),
      AlgebraicGeometry.Etale g ∧ AlgebraicGeometry.Surjective g ∧
        ∃ (σ : baseChange g (ofOver (Over.mk π)) ⟶ baseChange g W),
          σ ≫ baseChangeMap g f = 𝟙 (baseChange g (ofOver (Over.mk π)))) ↔
      ∃ (U' : Scheme.{u}) (g : U' ⟶ U),
        AlgebraicGeometry.Etale g ∧ AlgebraicGeometry.Surjective g ∧
          IsSplitEpi (baseChangeMap g f))

end AlgebraicGeometry.AlgebraicSpace
