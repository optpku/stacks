module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Inequalities
public import stacks_project.Chap52.Definition_52_19_1_Completion

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- Definition 52.19.1 (1): the ordinary completed-stalk `(a, b)`-inequalities. -/
@[stacks 0EJ3]
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.SatisfiesInequalities (A := A) :
  (S : AffineAlgebraizationSetup A) →
    CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) →
    ℤ → ℤ → Prop)

/- Definition 52.19.1 (2): the strict completed-stalk `(a, b)`-inequalities. -/
@[stacks 0EJ3]
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.SatisfiesStrictInequalities (A := A) :
  (S : AffineAlgebraizationSetup A) →
    CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) →
    ℤ → ℤ → Prop)

/- The pointwise ordinary inequalities application theorem. -/
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.satisfiesInequalities_apply (A := A))

/- The pointwise strict inequalities application theorem. -/
#check (AlgebraicGeometry.Scheme.CoherentFormalModules.satisfiesStrictInequalities_apply (A := A))

end AlgebraicGeometry.Scheme.CoherentFormalModules
