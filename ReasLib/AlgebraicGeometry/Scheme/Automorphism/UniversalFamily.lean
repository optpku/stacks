/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Endomorphism
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Universal automorphism families of schemes over a field
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.Automorphism

variable {k : Type u} [Field k]

/-- Iterated pullback along a morphism of schemes over a field agrees with direct pullback. -/
def pullbackFamilyIso (X : SchemeOverField k) {G T : SchemeOverField k} (f : T ⟶ G) :
    (Over.pullback f.left).obj ((Over.pullback G.hom).obj X) ≅
      (Over.pullback T.hom).obj X :=
  ((Over.pullbackComp f.left G.hom).app X).symm ≪≫
    eqToIso (congrArg (fun h => (Over.pullback h).obj X) f.w)

/-- Pull back an automorphism family along a morphism of schemes over the base field. -/
def pullbackFamily (X : SchemeOverField k) {G T : SchemeOverField k} (f : T ⟶ G)
    (α : Aut ((Over.pullback G.hom).obj X)) : Aut ((Over.pullback T.hom).obj X) :=
  Aut.autMulEquivOfIso (pullbackFamilyIso X f) ((Over.pullback f.left).mapAut _ α)

/-- An automorphism family is universal if its pullbacks classify automorphisms after every
base change by a scheme over the base field. -/
def IsUniversalFamily (X : SchemeOverField k) {G : SchemeOverField k}
    (α : Aut ((Over.pullback G.hom).obj X)) : Prop :=
  ∀ T : SchemeOverField k, Function.Bijective (fun f : T ⟶ G => pullbackFamily X f α)

end AlgebraicGeometry.SchemeOverField.Automorphism
