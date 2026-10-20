module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalPolynomialSystem.LocalModel
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace UniversalPolynomialSystem

/- Lemma 49.10.7: a locally quasi-finite syntomic morphism is, near every source
point, a cartesian base change of one of the universal morphisms from Example 49.10.5. -/
@[stacks 0FKA]
#check (UniversalPolynomialSystem.exists_localModel :
  ∀ {X Y : Scheme.{0}} (f : Y ⟶ X)
    [LocallyQuasiFinite f] [Syntomic f] (y : Y),
    ∃ (n d : ℕ+) (U : X.Opens) (V : Y.Opens) (hy : y ∈ V)
      (h : V ≤ f ⁻¹ᵁ U)
      (a : V.toScheme ⟶ (quasiFiniteOpen n d).toScheme)
      (b : U.toScheme ⟶ baseScheme n d),
      IsPullback a (f.resLE U V h)
        ((quasiFiniteOpen n d).ι ≫ projection n d) b)

end UniversalPolynomialSystem
