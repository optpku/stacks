/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.WeaklyAssociatedPoints
import StacksCheckRecall

/-!
# Definition 31.5.1

The weakly associated points of scheme modules and schemes are owned by
`ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints` and
`ReasLib.AlgebraicGeometry.Scheme.WeaklyAssociatedPoints`.
-/

@[expose] public section

universe u

/- Definition 31.5.1: canonical weakly-associated-point owners for scheme modules and schemes. -/
@[stacks 056L] #check (@AlgebraicGeometry.Scheme.Modules.weaklyAssociatedAt :
  {X : AlgebraicGeometry.Scheme.{u}} → X.Modules → X → Prop)

#check (@AlgebraicGeometry.Scheme.Modules.weakAss :
  {X : AlgebraicGeometry.Scheme.{u}} → X.Modules → Set X)
#check (@AlgebraicGeometry.Scheme.Modules.mem_weakAss_iff :
  {X : AlgebraicGeometry.Scheme.{u}} → (F : X.Modules) → (x : X) →
    (x ∈ F.weakAss ↔ F.weaklyAssociatedAt x))
#check (@AlgebraicGeometry.Scheme.weakAss :
  (X : AlgebraicGeometry.Scheme.{u}) → Set X)
#check (@AlgebraicGeometry.Scheme.mem_weakAss_iff :
  (X : AlgebraicGeometry.Scheme.{u}) → (x : X) →
    (x ∈ X.weakAss ↔
      AlgebraicGeometry.Scheme.Modules.weaklyAssociatedAt
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) x))
#check (@AlgebraicGeometry.Scheme.mem_weakAss_iff_isWeaklyAssociatedToModule :
  (X : AlgebraicGeometry.Scheme.{u}) → (x : X) →
    (x ∈ X.weakAss ↔
      Ideal.IsWeaklyAssociatedToModule (X.presheaf.stalk x)
        (AlgebraicGeometry.RingedSpace.stalkModuleCat
          (SheafOfModules.unit X.ringCatSheaf : X.Modules)
          (x : X.toRingedSpace))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))))
