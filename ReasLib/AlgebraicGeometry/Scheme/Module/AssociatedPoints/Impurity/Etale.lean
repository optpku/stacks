/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.BaseChange
import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.EtaleNeighborhood

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Impurity

/-- For a finite type morphism, if an impurity has a base-change morphism that is
quasi-finite at its special point, then there exists an impurity whose pointed base
change is an elementary étale neighbourhood. -/
theorem exists_elementary_of_quasiFiniteAt {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
    [Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
    (h_impurity : ∃ I : Impurity F f s,
      Hom.FiniteType.QuasiFiniteAt I.g I.specialPoint) :
    ∃ I : Impurity F f s, I.IsElementary := sorry

/-- For a locally finite type morphism, if an impurity has a base-change morphism that is
quasi-finite at its special point, then there exists an impurity whose pointed base
change is an elementary étale neighbourhood. -/
theorem exists_elementary_of_quasiFiniteAt_of_locallyOfFiniteType
    {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S) [LocallyOfFiniteType f]
    [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
    (h_impurity : ∃ I : Impurity F f s,
      Hom.FiniteType.QuasiFiniteAt I.g I.specialPoint) :
    ∃ I : Impurity F f s, I.IsElementary := sorry

/-- For a locally finite type morphism and a finite type quasicoherent module, there are
no elementary impurities above `s` if and only if no impurity above `s` has a base-change
morphism that is quasi-finite at its special point. -/
theorem noElementary_iff_noQuasiFiniteAt {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] (s : S) :
    (∀ I : Impurity F f s, ¬ I.IsElementary) ↔
      ¬ ∃ I : Impurity F f s, Hom.FiniteType.QuasiFiniteAt I.g I.specialPoint := sorry

end AlgebraicGeometry.Scheme.Modules.Impurity
