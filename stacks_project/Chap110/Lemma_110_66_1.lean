module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.NonEffectiveDescent

/-!
# Non-effective descent data for projective schemes
-/

@[expose] public section

universe u

open CategoryTheory

open AlgebraicGeometry

/- Lemma 110.66.1: there exists an étale covering of schemes and a relative scheme
descent datum whose component morphisms are projective, but the datum is not effective
in the category of schemes. -/
@[stacks 08KF]
#check (AlgebraicGeometry.Projective.exists_etaleCover_descent_not_isEffective :
    ∃ (S : Scheme.{u}) (𝒰 : S.Cover.{u} Scheme.etalePrecoverage)
      (D : Scheme.DescentData 𝒰.X 𝒰.f),
      (∀ i, Projective (D.obj i).hom) ∧ ¬ D.IsEffective)

/- There exists an étale surjective scheme morphism and a relative descent datum
whose component morphism is projective, but the datum is not effective in the
category of schemes. -/
#check (AlgebraicGeometry.Projective.exists_etaleHom_descent_not_isEffective :
    ∃ (X S : Scheme.{u}) (f : X ⟶ S)
      (D : Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f)),
      Etale f ∧ Surjective f ∧ Projective (D.obj PUnit.unit).hom ∧ ¬ D.IsEffective)

/- The morphism property of being projective does not satisfy effective étale descent. -/
#check (AlgebraicGeometry.Projective.not_satisfiesDescentEtale :
    ¬ MorphismProperty.SatisfiesDescent (@Projective : MorphismProperty Scheme.{u})
        DescentTopology.etale)
