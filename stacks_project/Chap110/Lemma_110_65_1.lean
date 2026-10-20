module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.NonLocality

/-!
# Being projective is not local on the base
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/- Lemma 110.65.1 (1): projectivity is not Zariski local on the base. -/
@[stacks 08J1] #check (AlgebraicGeometry.Projective.not_isZariskiLocalAtTarget :
    ¬ IsZariskiLocalAtTarget (@Projective : MorphismProperty Scheme.{u}))

/- Lemma 110.65.1 (2): quasi-projectivity is not Zariski local on the base. -/
@[stacks 08J1] #check (AlgebraicGeometry.QuasiProjective.not_isZariskiLocalAtTarget :
    ¬ IsZariskiLocalAtTarget (@QuasiProjective : MorphismProperty Scheme.{u}))

/- Lemma 110.65.1 (3): projectivity is not fpqc local on the base. -/
@[stacks 08J1] #check (AlgebraicGeometry.Projective.not_isLocalAtTargetFpqc :
    ¬ MorphismProperty.IsLocalAtTarget (@Projective : MorphismProperty Scheme.{u})
        Scheme.fpqcPrecoverage)

/- Lemma 110.65.1 (4): quasi-projectivity is not fpqc local on the base. -/
@[stacks 08J1] #check (AlgebraicGeometry.QuasiProjective.not_isLocalAtTargetFpqc :
    ¬ MorphismProperty.IsLocalAtTarget (@QuasiProjective : MorphismProperty Scheme.{u})
        Scheme.fpqcPrecoverage)

/- A scheme morphism may be locally projective but not projective. -/
#check (AlgebraicGeometry.Projective.exists_locallyProjective_not_projective :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y), LocallyProjective f ∧ ¬ Projective f)

/- A scheme morphism may be locally quasi-projective but not quasi-projective. -/
#check (AlgebraicGeometry.QuasiProjective.exists_locallyQuasiProjective_not_quasiProjective :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y), LocallyQuasiProjective f ∧ ¬ QuasiProjective f)

end AlgebraicGeometry
