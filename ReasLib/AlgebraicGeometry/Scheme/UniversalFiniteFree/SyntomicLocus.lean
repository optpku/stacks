/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.UniversalFiniteFree
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace UniversalFiniteFreeAlgebra

/-- For the universal finite locally free family of rank `d`, an open base subscheme
classifies exactly those base changes whose induced family morphism is syntomic. -/
theorem exists_open_syntomicBaseChange_iff (d : ℕ+) :
    ∃ U : (baseScheme d).Opens,
      ∀ {X : Scheme.{0}} (f : X ⟶ baseScheme d),
        (∃ g : X ⟶ U.toScheme, g ≫ U.ι = f) ↔
          Syntomic (pullback.snd (projection d) f) := sorry

/-- The open subscheme of the universal finite locally free family of rank `d`
is smooth over `Spec (ℤ)` whenever it classifies exactly the syntomic base
changes of the universal family. -/
theorem syntomicLocusSmooth (d : ℕ+) (U_d : (baseScheme d).Opens)
    (hU_d : ∀ {X : Scheme.{0}} (f : X ⟶ baseScheme d),
      (∃ g : X ⟶ U_d.toScheme, g ≫ U_d.ι = f) ↔
        Syntomic (pullback.snd (projection d) f)) :
    Smooth (U_d.ι ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (CoefficientRing d)))) := sorry

/-- The restricted universal finite locally free family over the syntomic locus
is smooth over `Spec (ℤ)`. -/
theorem syntomicLocusFamilySmooth (d : ℕ+) (U_d : (baseScheme d).Opens)
    (hU_d : ∀ {X : Scheme.{0}} (f : X ⟶ baseScheme d),
      (∃ g : X ⟶ U_d.toScheme, g ≫ U_d.ι = f) ↔
        Syntomic (pullback.snd (projection d) f)) :
    Smooth ((projection d ∣_ U_d) ≫ U_d.ι ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (CoefficientRing d)))) := sorry

/-- The restricted universal finite locally free family over the syntomic locus
is not smooth over that locus when its rank is at least two. -/
theorem syntomicLocusProjection_not_smooth (d : ℕ+) (U_d : (baseScheme d).Opens)
    (hU_d : ∀ {X : Scheme.{0}} (f : X ⟶ baseScheme d),
      (∃ g : X ⟶ U_d.toScheme, g ≫ U_d.ι = f) ↔
        Syntomic (pullback.snd (projection d) f))
    (hd : 2 ≤ d) : ¬ Smooth (projection d ∣_ U_d) := sorry

end UniversalFiniteFreeAlgebra
