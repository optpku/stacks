/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent.OpenCover
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 35.2.4 (1): every quasi-coherent descent datum on a scheme open cover is effective. -/
@[stacks 023E] #check
  (@AlgebraicGeometry.Scheme.QCoh.OpenCover.DescentData.isEffective :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (𝒰 : S.OpenCover.{v})
      (D : AlgebraicGeometry.Scheme.QCoh.DescentData
        (fun i : 𝒰.I₀ ↦ 𝒰.X i) (fun i ↦ 𝒰.f i)),
      (AlgebraicGeometry.Scheme.QCoh.OpenCover.restriction 𝒰).essImage D)

/- Lemma 35.2.4 (2): restriction from global quasi-coherent modules to descent data on a scheme
open cover is fully faithful. -/
@[stacks 023E] #check
  (@AlgebraicGeometry.Scheme.QCoh.OpenCover.restriction.fullyFaithful :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (𝒰 : S.OpenCover.{v}),
      Nonempty (AlgebraicGeometry.Scheme.QCoh.OpenCover.restriction 𝒰).FullyFaithful)
