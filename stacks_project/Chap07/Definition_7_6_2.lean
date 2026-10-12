/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.IndexedSite
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C]

/- Definition 7.6.2: a site is a category C together with a set Cov(C) of
families of morphisms with fixed target {Uᵢ ⟶ U}_{i ∈ I}, called coverings of
C, such that (1) every isomorphism V ⟶ U is a singleton covering, (2) coverings
are stable under bind of covering families, and (3) pullbacks of covering
arrows along any V ⟶ U exist and the pulled-back family covers V for some
choice of pullback objects. The indexed covering collection is explicit;
no global pullbacks or closure under arbitrary reindexing are assumed. -/
@[stacks 00VH] #check (CategoryTheory.PreZeroHypercover.IsSite :
  (∀ target : C, Set (CategoryTheory.PreZeroHypercover.{w} target)) → Prop)
