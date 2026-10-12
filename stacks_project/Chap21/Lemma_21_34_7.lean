/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom.Complex
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.34.7

The underlying internal-Hom map is owned by the generic closed-monoidal API, while its
quasi-isomorphism property for K-injective ringed-site complexes is owned by the reusable
ringed-site leaf.  The chapter introduces no parallel map or specialized notation.
-/

/- The canonical internal-Hom map induced contravariantly in the source and covariantly in the
target. -/
@[stacks 0A95 "internal-Hom map"] #check
  @CategoryTheory.MonoidalClosed.Source.map

/- Lemma 21.34.7 (0A95): quasi-isomorphisms in both variables induce a quasi-isomorphism between
internal-Hom complexes when both targets are K-injective. -/
@[stacks 0A95 "quasi-isomorphism of internal-Hom complexes"] #check
  @SheafOfModules.RingedSite.IHom.quasiIso_map
