module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalPolynomialSystem
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.QuasiFinite

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

namespace UniversalPolynomialSystem

/-- Every locally quasi-finite syntomic morphism of schemes is locally a cartesian
base change of a universal polynomial system. -/
theorem exists_localModel {X Y : Scheme.{0}} (f : Y ⟶ X)
    [LocallyQuasiFinite f] [Syntomic f] (y : Y) :
    ∃ (n d : ℕ+) (U : X.Opens) (V : Y.Opens) (hy : y ∈ V)
      (h : V ≤ f ⁻¹ᵁ U)
      (a : V.toScheme ⟶ (quasiFiniteOpen n d).toScheme)
      (b : U.toScheme ⟶ baseScheme n d),
      IsPullback a (f.resLE U V h)
        ((quasiFiniteOpen n d).ι ≫ projection n d) b := sorry

end UniversalPolynomialSystem
