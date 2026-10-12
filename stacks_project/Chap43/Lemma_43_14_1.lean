/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Coherent.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tor.Coherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure
open scoped RingedTensor

universe u

/- Lemma 43.14.1 (1): on a locally Noetherian scheme, every Tor sheaf of two
coherent `𝒪_X`-modules is coherent. -/
@[stacks 0AZS] #check
  (AlgebraicGeometry.Scheme.Modules.torRight_isCoherent :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      (F G : X.Modules) [F.IsCoherent] [G.IsCoherent] (p : ℕ),
      (RingedSpace.ModuleDerived.torRight p F G).IsCoherent)

/- Lemma 43.14.1 (2): on a locally Noetherian scheme, the derived tensor product
of two bounded-above complexes with coherent cohomology is again bounded above
with coherent cohomology. -/
@[stacks 0AZS] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.derivedTensor_boundedAbove_cohomology_coherent :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      (L K : RingedSpace.ModuleDerived X.toRingedSpace),
      (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L →
      DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L →
      (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) K →
      DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K →
      (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) (L ⊗^L K) ∧
        DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (L ⊗^L K))
