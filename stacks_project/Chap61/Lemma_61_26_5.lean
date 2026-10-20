module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.ClosedOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/- Lemma 61.26.5: if `i : Z ⟶ X` is a closed immersion and
`j = (closedImmersionComplement i).ι` is the quasi-compact open complement
inclusion, then for every abelian sheaf `F` on `X_proétale` the canonical
sequence `0 ⟶ j_! (j⁻¹ F) ⟶ F ⟶ i_* (i⁻¹ F) ⟶ 0` is short exact, where all
functors are the small pro-étale functors `abelianExtensionByZero`,
`restrictionSheaf`, `smallPushforward`, and `smallInverseImage`. -/
@[stacks 09AH] #check
  (AlgebraicGeometry.Scheme.ProEt.abelianClosedOpenShortComplex_shortExact :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [QuasiCompact (closedImmersionComplement i).ι]
      (F : Sheaf (topology X) AddCommGrpCat.{u + 1}),
      (abelianClosedOpenShortComplex i F).ShortExact)

end AlgebraicGeometry.Scheme.ProEt

