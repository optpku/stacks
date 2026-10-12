/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Precoverage.Continuous
import StacksCheckRecall

@[expose] public section

/- Definition 7.13.1: a functor u : C ⥤ D of sites is continuous when every
covering {Vᵢ ⟶ V} of C is sent to a covering {u(Vᵢ) ⟶ u(V)} of D, and for every
morphism T ⟶ V the comparison u(T ×_V Vᵢ) ⟶ u(T) ×_{u(V)} u(Vᵢ) is an
isomorphism. This is the selected-cover owner Functor.Precoverage.IsContinuous,
not mathlib's sheaf-layer Functor.IsContinuous. -/
@[stacks 00WV] #check @CategoryTheory.Functor.Precoverage.IsContinuous
