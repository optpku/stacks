/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Lift
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoPullbackCone.Pseudofunctor.Basic

/-!
# Forgetting locally induced pseudopullback cones

This leaf owns the concrete forgetful cone map and its readable cone pseudofunctor.  Field
formulas and the bilimit transfer theorem are kept in the computation and bilimit leaves.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe uA uB vB wB

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {A : Type uA} {B : Type uB} [Bicategory.{wB, vB} B]
variable {baseObj : A → B} {Q : Bicategory.HomProperty baseObj} [Q.IsMultiplicative]
variable {x y z : Bicategory.LocallyInducedBicategory B baseObj Q}
variable {f : x ⟶ z} {g : y ⟶ z}

/-- Forget a pseudo-pullback cone in a locally induced bicategory to its ambient bicategory. -/
def forgetLocallyInduced (P : PseudoPullbackCone f g) :
    PseudoPullbackCone f.obj g.obj :=
  ((Bicategory.LocallyInducedBicategory.forget B baseObj Q).toPseudofunctor).mapPseudoPullbackCone P

variable (f) (g) in
/-- Forgetting readable pseudo-pullback cones from a locally induced bicategory to the ambient
bicategory is pseudofunctorial on cones, cone morphisms, and cone `2`-morphisms. The source
cospan legs are explicit because this global owner has no cone value from which to recover them. -/
def forgetLocallyInduced.pseudofunctor :
  Pseudofunctor (PseudoPullbackCone f g)
      (PseudoPullbackCone f.obj g.obj) :=
  Pseudofunctor.mapPseudoPullbackCone.pseudofunctor
    f g ((Bicategory.LocallyInducedBicategory.forget B baseObj Q).toPseudofunctor)

/- Data audit: both owners apply the explicit ambient forgetful pseudofunctor to the supplied
cone data. Their object, `1`-morphism, and `2`-morphism actions introduce no new choices;
any `sorryAx` dependency is confined to inherited law, naturality, and coherence fields. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
