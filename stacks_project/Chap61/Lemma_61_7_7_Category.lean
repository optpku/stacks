/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.IndEtale.BaseChange

@[expose] public section

open CategoryTheory TensorProduct

universe u v w

/-!
# The category of ind-étale algebras

The reusable object property, full subcategory, and base-change construction
are owned by `ReasLib.Algebra.Category.CommAlgCat.IndEtale`.
-/

/- The promoted ind-étale object property. -/
#check (CommAlgCat.IndEtale.indEtale :
  ∀ (R : Type u) [CommRing R], ObjectProperty (CommAlgCat.{v} R))

/- The defining characterization of ind-étale commutative algebra objects. -/
#check (CommAlgCat.IndEtale.indEtale_iff :
  ∀ {R : Type u} [CommRing R] (S : CommAlgCat.{v} R),
    CommAlgCat.IndEtale.indEtale R S ↔ (algebraMap R S).IndEtale)

/- Tensor-product base change preserves ind-étaleness. -/
#check (CommAlgCat.IndEtale.baseChange_indEtale :
  ∀ (R : Type u) [CommRing R] (S : Type w) [CommRing S] [Algebra R S]
    (A : CommAlgCat.IndEtale.{v} R),
    (algebraMap S (S ⊗[R] A)).IndEtale)

/- Reduction modulo an ideal is the specialized base-change functor. -/
#check (CommAlgCat.IndEtale.reduction :
  ∀ {A : Type u} [CommRing A] (I : Ideal A),
    CommAlgCat.IndEtale.{u} A ⥤ CommAlgCat.IndEtale.{u} (A ⧸ I))
