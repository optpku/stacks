/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Transport
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.Ring.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Basic

/-!
# Tensor product of modules on algebraic spaces

The structure sheaf of an algebraic space is the commutative global-sections sheaf on the small
étale site. Transporting the canonical ringed-site tensor product along restriction of scalars
yields a monoidal structure on algebraic-space modules.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Monoidal
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The forgetful image of the commutative structure sheaf is isomorphic to `𝒪_X`. -/
def commRingSheafIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (commStructureSheaf X) ≅
      structureSheaf X :=
  (fullyFaithfulSheafToPresheaf (smallEtaleTopology X) RingCat.{u}).preimageIso <|
    Functor.associator (smallEtaleToScheme X).op Scheme.Γ
      (forget₂ CommRingCat.{u} RingCat.{u})

namespace Modules

/-- Restriction of scalars along `commRingSheafIso` identifies modules over the commutative
presentation of `𝒪_X` with `X.Modules`. -/
def commModulesEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ringedSiteModuleCategory (smallEtaleTopology X) (commStructureSheaf X) ≌ X.Modules :=
  SheafOfModules.Restriction.equivalenceOfIso (commRingSheafIso X)

/-- The canonical tensor product on algebraic-space modules, transported from the commutative
ringed-site construction. -/
@[instance_reducible, instance]
noncomputable def instMonoidalCategory {S : Scheme.{u}} (X : AlgebraicSpace S) :
    MonoidalCategory X.Modules :=
  Monoidal.transport (commModulesEquivalence X)

end Modules

end AlgebraicGeometry.AlgebraicSpace
