module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LowerShriek
import StacksCheckRecall

@[expose] public section

open CategoryTheory RingedSite.Cocontinuous
open SheafOfModules.Localization

noncomputable section

universe z uC vC uD vD w

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
variable (R : Sheaf K RingCat.{w})

/-!
# Equation 21.37.2.1

The derived adjunction identifies maps into exact derived inverse image with maps out of derived
lower shriek. The total-derived models and their absolute-derived pair certificate are supplied.
-/

variable [UnivLE.{max uC vC, z}] [UnivLE.{max uD vD, z}]
variable [Functor.HasLeftDerivedFunctor
  (moduleLowerShriek.toDerived (J := J) (K := K) f R)
  (RingedSite.Hom.ModuleQis.{z} (moduleInverseImage.source (J := J) (K := K) f R))]
variable [moduleLowerShriek.derived.HasPair (J := J) (K := K) f R]
variable (M : RingedSite.Hom.ModuleDerived.{z}
  (moduleInverseImage.source (J := J) (K := K) f R))
variable (N : RingedSite.Hom.ModuleDerived.{z} (moduleInverseImage.target (K := K) R))

/- Equation 21.37.2.1 (07AD): `(M ⟶ g^* N) ≃ (Lg_! M ⟶ N)`. -/
@[stacks 07AD "derived lower-shriek Hom equivalence"]
#check (moduleLowerShriek.derived.homEquivSymm (J := J) (K := K) f R M N :
  (M ⟶ (moduleInverseImage.derived (J := J) (K := K) f R).obj N) ≃
    ((moduleLowerShriek.derived (J := J) (K := K) f R).obj M ⟶ N))
