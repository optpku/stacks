module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomFunctor.ClosedImmersion

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 99.3.7: if `i : X' ⟶ X` is a closed immersion of algebraic spaces over `B`,
`F` is a quasi-coherent `𝒪_X`-module, and `G'` is a quasi-coherent `𝒪_{X'}`-module,
then `Hom(F, i_* G')` and `Hom(i^* F, G')` are canonically identified as functors on
`(Sch/B)`. -/
@[stacks 08K5] #check (AlgebraicGeometry.AlgebraicSpace.Modules.homFunctor_closedImmersion :
  ∀ {S : Scheme.{u}} {B X X' : AlgebraicSpace S}
    (f : X ⟶ B) (f' : X' ⟶ B) (i : X' ⟶ X) (h_over : i ≫ f = f')
    [IsClosedImmersion i] (F : X.Modules) (G' : X'.Modules)
    [F.IsQuasicoherent] [G'.IsQuasicoherent],
    IsIsomorphic (homFunctor f F ((pushforward i).obj G'))
      (homFunctor f' ((pullback i).obj F) G'))

/- Pointwise form of the closed-immersion identification of Hom functors: at a scheme
over `B`, the two base-changed Hom-types are equivalent. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.homFunctor_closedImmersion_obj :
  ∀ {S : Scheme.{u}} {B X X' : AlgebraicSpace S}
    (f : X ⟶ B) (f' : X' ⟶ B) (i : X' ⟶ X) (h_over : i ≫ f = f')
    [IsClosedImmersion i] (F : X.Modules) (G' : X'.Modules)
    [F.IsQuasicoherent] [G'.IsQuasicoherent] (σ : SchemeOver B),
    Nonempty
      ((baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom ((pushforward i).obj G')) ≃
        (baseChangeModule f' σ.hom ((pullback i).obj F) ⟶ baseChangeModule f' σ.hom G')))

end AlgebraicGeometry.AlgebraicSpace.Modules
