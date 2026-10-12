/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.Representability
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

universe u

/- Lemma 27.16.3: in Situation 27.15.1, the degree-`d` relative-`Proj` functor associated to
fixed-degree quadruples is representable by a scheme. -/
@[stacks 01NV] #check
  (AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor.isRepresentable :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf} {d : ℕ}
      [𝒜.IsCommutative]
      (F_d : AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor S 𝒜 d)
      (associatedToQuadruples : F_d.IsAssociatedToQuadruples),
      F_d.toFunctor.IsRepresentable)
