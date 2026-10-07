module

public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation.ChangeOfRings
import StacksCheckRecall

@[expose] public section

universe u v

namespace ModuleCat


/- Remark 56.4.4: combining Remarks 56.3.10 and 56.4.2 and Lemma 56.4.3, ring maps
`A →+* B` are in bijection with isomorphism classes of right-exact monoidal functors
`Mod^fp_A ⥤ Mod^fp_B`. -/
@[stacks 0GP7] #check
  (ModuleCat.ringHom_bijective_isoClass_rightExactMonoidalFp :
    ∀ {A : Type u} [CommRing A] {B : Type v} [CommRing B],
      Function.Bijective
        (ModuleCat.ringHom_to_rightExactMonoidalFpIsoClass :
          (A →+* B) → ModuleCat.rightExactMonoidalFpIsoClass A B))

end ModuleCat
