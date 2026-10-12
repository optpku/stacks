/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Finite
import Mathlib.Tactic.CrossRefAttribute

/-!
# The category of etale algebras

This leaf packages the existing `CommAlgCat.etale` object property as a category and supplies its
canonical tensor-product base-change functor. It is the non-finite analogue of Mathlib's
`CommAlgCat.FiniteEtale` API.

@stack 0ALI
-/

@[expose] public section

open CategoryTheory TensorProduct

universe v w u

namespace CommAlgCat

/-- The full subcategory of etale `R`-algebras. -/
@[stacks 0ALI "category of etale algebras"]
abbrev Etale (R : Type u) [CommRing R] : Type _ :=
  (etale.{v} R).FullSubcategory

/-- An etale algebra object coerces to its underlying carrier type. -/
instance {R : Type u} [CommRing R] : CoeSort (Etale.{v} R) (Type v) :=
  ⟨fun S ↦ S.obj⟩

/-- The defining etaleness property of an object of `CommAlgCat.Etale R`. -/
instance {R : Type u} [CommRing R] (S : Etale.{v} R) : Algebra.Etale R S :=
  S.property

/-- Build an object of `CommAlgCat.Etale R` from an etale `R`-algebra. -/
@[stacks 0ALI "etale algebra as a categorical object"]
abbrev Etale.of (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    [Algebra.Etale R S] : Etale.{v} R where
  obj := .of R S
  property := inferInstance

/-- Build a morphism of etale algebras from an algebra homomorphism. -/
@[stacks 0ALI "morphism of etale algebra objects"]
abbrev Etale.ofHom {R : Type u} [CommRing R] {S T : Type v}
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra.Etale R S] [Algebra.Etale R T] (f : S →ₐ[R] T) :
    Etale.of R S ⟶ Etale.of R T where
  hom := CommAlgCat.ofHom f

/-- Tensor-product base change on etale algebras. -/
@[stacks 0ALI "base change of etale algebras"]
def Etale.baseChange (R : Type u) [CommRing R] (S : Type w) [CommRing S] [Algebra R S] :
    Etale.{v} R ⥤ Etale.{max w v} S where
  obj A := .of S (S ⊗[R] A)
  map {A B} f := Etale.ofHom (Algebra.TensorProduct.map (.id _ _) f.hom.hom)

/-- Reduction modulo `I` on etale algebras is the canonical base-change functor along
`R → R / I`. -/
@[stacks 0ALI "reduction of etale algebras"]
abbrev Etale.reduction {R : Type u} [CommRing R] (I : Ideal R) :
    Etale.{u} R ⥤ Etale.{u} (R ⧸ I) :=
  Etale.baseChange R (R ⧸ I)

end CommAlgCat
