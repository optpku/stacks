/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.UniversalFiniteFree.SyntomicLocus

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace UniversalFiniteFreeAlgebra

/-- Every finite syntomic morphism is locally a cartesian base change of the
universal finite free family over its syntomic locus. -/
theorem exists_localModel {X Y : Scheme.{0}} (f : Y ⟶ X)
    [IsFinite f] [Syntomic f] (x : X) :
    ∃ (d : ℕ+) (U : X.Opens) (hx : x ∈ U)
      (U_d : (baseScheme d).Opens)
      (hU_d : ∀ {T : Scheme.{0}} (g : T ⟶ baseScheme d),
        (∃ h : T ⟶ U_d.toScheme, h ≫ U_d.ι = g) ↔
          Syntomic (pullback.snd (projection d) g))
      (a : (f ⁻¹ᵁ U).toScheme ⟶ (projection d ⁻¹ᵁ U_d).toScheme)
      (b : U.toScheme ⟶ U_d.toScheme),
      IsPullback a (f ∣_ U) (projection d ∣_ U_d) b := sorry

end UniversalFiniteFreeAlgebra
