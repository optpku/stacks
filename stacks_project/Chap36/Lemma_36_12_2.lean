/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

/- Lemma 36.12.2: for an fpqc covering family `family` of a scheme `X`, an object
with quasicoherent cohomology is `m`-pseudo-coherent if and only if every derived
pullback along a member of `family` is `m`-pseudo-coherent. -/
@[stacks 09UE] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.isMPseudoCoherent_iff_fpqcCovering :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      (family : ι → Over X) (hfamily : AlgebraicGeometry.Scheme.FpqcCovering family)
      (E : DerivedCategory.CohomologyIn
        (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
      (m : ℤ),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent E.obj m ↔
        ∀ i : ι, AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent
          ((AlgebraicGeometry.Scheme.DerivedQCoh.pullback (family i).hom).obj E).obj m)
