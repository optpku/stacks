/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Support
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/- Lemma 56.6.3: for a quasi-compact and quasi-separated scheme `X` and a
finitely presented quasi-coherent module `F`, the quasi-coherent modules whose
support is contained in the support of `F` form the smallest Serre object
property containing `F` and closed under arbitrary direct sums. -/
@[stacks 0GPG]
#check (AlgebraicGeometry.Scheme.QCoh.support_eq_serreCoproductClosure :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (F : Scheme.QCoh X) [F.obj.IsFinitePresentation],
      (fun E : Scheme.QCoh X ↦
        Scheme.Modules.moduleSupport E.obj ⊆ Scheme.Modules.moduleSupport F.obj) =
        sInf {P : ObjectProperty (Scheme.QCoh X) |
          P F ∧ P.IsSerreClass ∧
            ∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I)})

end AlgebraicGeometry.Scheme.QCoh
