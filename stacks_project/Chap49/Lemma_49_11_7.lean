module

public import ReasLib.AlgebraicGeometry.Scheme.UniversalFiniteFree.LocalModel
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace UniversalFiniteFreeAlgebra

/- Lemma 49.11.7: every finite syntomic morphism is, near each target point,
a cartesian base change of the universal finite free family restricted to its
syntomic locus. -/
@[stacks 0FL4] #check
  (UniversalFiniteFreeAlgebra.exists_localModel :
    ∀ {X Y : Scheme.{0}} (f : Y ⟶ X),
      [IsFinite f] → [Syntomic f] → (x : X) →
        ∃ (d : ℕ+) (U : X.Opens) (hx : x ∈ U)
          (U_d : (UniversalFiniteFreeAlgebra.baseScheme d).Opens)
          (hU_d : ∀ {T : Scheme.{0}}
            (g : T ⟶ UniversalFiniteFreeAlgebra.baseScheme d),
            (∃ h : T ⟶ U_d.toScheme, h ≫ U_d.ι = g) ↔
              Syntomic
                (pullback.snd (UniversalFiniteFreeAlgebra.projection d) g))
          (a : (f ⁻¹ᵁ U).toScheme ⟶
            (UniversalFiniteFreeAlgebra.projection d ⁻¹ᵁ U_d).toScheme)
          (b : U.toScheme ⟶ U_d.toScheme),
          IsPullback a (f ∣_ U)
            (UniversalFiniteFreeAlgebra.projection d ∣_ U_d) b)

end UniversalFiniteFreeAlgebra
