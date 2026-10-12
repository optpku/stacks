/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Pairing

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open scoped DerivedExt

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DerivedQCoh
namespace ProperDualizingComplex

/- Remark 48.27.3 -/
@[stacks 0FVX]
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.pairingWith_module_naturality :
    {k : Type u} → [Field k] → {X : Scheme.{u}} →
    (e : fieldObject k ≅ ModuleCat.of k k) →
    (f : X ⟶ Spec (CommRingCat.of k)) → [IsProper f] →
    (i : ℤ) → {F G : QCoh X} → (φ : F ⟶ G) →
    (pairingWith e f i (moduleObject F)).comp
        (((DerivedExt.bifunctor f i).map
          ((DerivedQCoh.inclusion X).map (moduleObjectMap φ)).op).app
            (properDualizingComplex f).obj).hom =
      (cohomologyOverFieldMap f (moduleObjectMap φ) (-i)).hom.dualMap.comp
        (pairingWith e f i (moduleObject G)))

#check pairingWith_naturality
#check pairingWith_module_naturality_apply

end ProperDualizingComplex
end DerivedQCoh
end Scheme
end AlgebraicGeometry
