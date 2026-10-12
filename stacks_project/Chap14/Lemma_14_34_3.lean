/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.SimplicialResolution.Realization
import StacksCheckRecall

@[expose] public section

/-!
@stack 08ND

# Contracting an adjunction resolution

This is the source-facing facade for Lemma 14.34.3.  Its primary statements use the canonical
resolution determined by the adjunction; arbitrary realizations remain available through
transport bridges in `ReasLib`.
-/

open CategoryTheory

universe uA uS vA vS

namespace CategoryTheory.Adjunction.SimplicialResolution

variable {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
variable {U : S ⥤ A} {V : A ⥤ S} (adj : U ⊣ V)

/- Lemma 14.34.3 (1): after postcomposition by the right adjoint, the canonical resolution
augmentation is a simplicial homotopy equivalence. -/
@[stacks 08ND "Lemma 14.34.3 (1)"]
#check (postcompose.isHomotopyEquivalence adj :
  SimplicialObject.IsHomotopyEquivalence (postcompose adj).hom)

/- Lemma 14.34.3 (2): after precomposition by the left adjoint, the canonical resolution
augmentation is a simplicial homotopy equivalence. -/
@[stacks 08ND "Lemma 14.34.3 (2)"]
#check (precompose.isHomotopyEquivalence adj :
  SimplicialObject.IsHomotopyEquivalence (precompose adj).hom)

/- The postcomposed resolution carries the order-reversed, last extra degeneracy, whose generic
owner supplies both a concrete contraction and the resulting homotopy equivalence. -/
#check (postcompose.lastExtraDegeneracy adj : (postcompose adj).LastExtraDegeneracy)
#check ((postcompose.lastExtraDegeneracy adj).section_ :
  (SimplicialObject.const (A ⥤ S)).obj (postcompose adj).right ⟶
    (postcompose adj).left)
#check ((postcompose.lastExtraDegeneracy adj).homotopy :
  SimplicialObject.Homotopy
    (𝟙 (postcompose adj).left)
    ((postcompose adj).hom ≫ (postcompose.lastExtraDegeneracy adj).section_))
#check (postcompose.hom_inv_id adj :
  SimplicialObject.Homotopic
    ((postcompose adj).hom ≫ postcompose.inverse adj) (𝟙 (postcompose adj).left))

/- The precomposed resolution carries Mathlib's standard initial extra degeneracy and hence its
canonical concrete contraction. -/
#check (precompose.extraDegeneracy adj : (precompose adj).ExtraDegeneracy)
#check ((precompose.extraDegeneracy adj).homotopy :
  SimplicialObject.Homotopy
    ((precompose adj).hom ≫ (precompose.extraDegeneracy adj).section_)
    (𝟙 (precompose adj).left))

/- Compatibility projections retain the previously exposed inverses and homotopy
equivalences. -/
#check (postcompose.homotopyEquiv adj :
  SimplicialObject.HomotopyEquiv (postcompose adj).left
    ((SimplicialObject.const (A ⥤ S)).obj V))
#check (postcompose.inverse adj :
  (SimplicialObject.const (A ⥤ S)).obj V ⟶ (postcompose adj).left)
#check (precompose.homotopyEquiv adj :
  SimplicialObject.HomotopyEquiv (precompose adj).left
    ((SimplicialObject.const (S ⥤ A)).obj U))
#check (precompose.inverse adj :
  (SimplicialObject.const (S ⥤ A)).obj U ⟶ (precompose adj).left)

/- The same construction is available for every realization of the comonad formulas, with the
inverse and both homotopies retained as a bundled equivalence rather than only as a property. -/
variable {X : SimplicialObject (A ⥤ A)} (hX : adj.toComonad.Realizes X)

#check (postcompose.realization.iso adj hX)
#check (postcompose.realization.lastExtraDegeneracy adj hX)
#check (postcompose.realization.inverse adj hX)
#check (postcompose.realization.homotopyEquiv adj hX)
#check (precompose.realization.iso adj hX)
#check (precompose.realization.extraDegeneracy adj hX)
#check (precompose.realization.inverse adj hX)
#check (precompose.realization.homotopyEquiv adj hX)

end CategoryTheory.Adjunction.SimplicialResolution
