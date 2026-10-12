/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.Etale

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Germ.MorphismProperty

/-- A property of morphisms of scheme germs is étale local on source-and-target when it is
invariant across every commutative square whose vertical arrows are étale. -/
def IsEtaleLocal (Q : CategoryTheory.MorphismProperty Germ) : Prop :=
  ∀ {U' V' U V : Germ} (a : U' ⟶ U) (h' : U' ⟶ V') (h : U ⟶ V) (b : V' ⟶ V)
    [Etale a] [Etale b], CommSq a h' h b → (Q h ↔ Q h')

/-- Characterization of source-and-target étale locality by commutative squares of germs. -/
theorem isEtaleLocal_iff (Q : CategoryTheory.MorphismProperty Germ) :
    IsEtaleLocal Q ↔
      ∀ {U' V' U V : Germ} (a : U' ⟶ U) (h' : U' ⟶ V')
        (h : U ⟶ V) (b : V' ⟶ V) [Etale a] [Etale b],
          CommSq a h' h b → (Q h ↔ Q h') := sorry

/-- Transport a source-and-target étale-local property across one commutative square of germs. -/
theorem IsEtaleLocal.iff_of {Q : CategoryTheory.MorphismProperty Germ} (hQ : IsEtaleLocal Q)
    {U' V' U V : Germ} (a : U' ⟶ U) (h' : U' ⟶ V') (h : U ⟶ V) (b : V' ⟶ V)
    [Etale a] [Etale b] (sq : CommSq a h' h b) : Q h ↔ Q h' := sorry

end AlgebraicGeometry.Scheme.Germ.MorphismProperty
