/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv.Products
public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv.Coproducts
import StacksCheckRecall

/-!
@stack 08Q4

# Source-facing bridge for Lemma 14.26.10

The product constructions for directed homotopies, zigzag homotopies, and homotopy equivalences
are owned by the corresponding ReasLib namespaces. The coproduct companion API is recalled in a
separate section so neither variance forces irrelevant pointwise-limit hypotheses on the other.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable {T : Type w}

section Products

variable {X Y : T → SimplicialObject C}
variable [FunctorCategory.HasPointwiseProduct X]
variable [FunctorCategory.HasPointwiseProduct Y]
variable {a b : ∀ t, X t ⟶ Y t}

section Finite

variable [Finite T]

/- Lemma 14.26.10 (1): finite products preserve simplicial homotopy equivalences. -/
@[stacks 08Q4 "Lemma 14.26.10 (1)"]
#check (HomotopyEquiv.piObj.nonempty (X := X) (Y := Y) :
  (∀ t, Nonempty (HomotopyEquiv (X t) (Y t))) →
    Nonempty (HomotopyEquiv (∏ᶜ X) (∏ᶜ Y)))

/- The reusable morphism-property form of clause (1). -/
#check (homotopyEquivalences.piMap (C := C) a :
  (∀ t, homotopyEquivalences C (a t)) →
    homotopyEquivalences C (Limits.Pi.map a))

/- The fixed-shape and aggregate finite-product stability interfaces. -/
#check homotopyEquivalences.products.ofFiniteShape
#check @homotopyEquivalences.products.finite

end Finite

/- Lemma 14.26.10 (2): products combine directed simplicial homotopies componentwise. -/
@[stacks 08Q4 "Lemma 14.26.10 (2)"]
#check (DirectedHomotopy.piMap (X := X) (Y := Y) :
  (∀ t, DirectedHomotopy (a t) (b t)) →
    DirectedHomotopy (Limits.Pi.map a) (Limits.Pi.map b))

section Finite

variable [Finite T]

/- Lemma 14.26.10 (3): finite products preserve the zigzag simplicial homotopy relation. -/
@[stacks 08Q4 "Lemma 14.26.10 (3)"]
#check (Homotopic.piMap (X := X) (Y := Y) :
  (∀ t, Homotopic (a t) (b t)) →
    Homotopic (Limits.Pi.map a) (Limits.Pi.map b))

end Finite

end Products

section Coproducts

variable {X Y : T → SimplicialObject C}
variable [FunctorCategory.HasPointwiseCoproduct X]
variable [FunctorCategory.HasPointwiseCoproduct Y]
variable {a b : ∀ t, X t ⟶ Y t}

/- The variance-dual reusable API combines directed homotopies over arbitrary coproducts. -/
#check (DirectedHomotopy.sigmaMap (X := X) (Y := Y) :
  (∀ t, DirectedHomotopy (a t) (b t)) →
    DirectedHomotopy (Limits.Sigma.map a) (Limits.Sigma.map b))

section Finite

variable [Finite T]

/- Finite coproducts preserve the zigzag simplicial homotopy relation. -/
#check (Homotopic.sigmaMap (X := X) (Y := Y) :
  (∀ t, Homotopic (a t) (b t)) →
    Homotopic (Limits.Sigma.map a) (Limits.Sigma.map b))

/- The structured and morphism-property forms of finite-coproduct stability. -/
#check (HomotopyEquiv.sigmaObj.nonempty (X := X) (Y := Y) :
  (∀ t, Nonempty (HomotopyEquiv (X t) (Y t))) →
    Nonempty (HomotopyEquiv (∐ X) (∐ Y)))

#check (homotopyEquivalences.sigmaMap (C := C) a :
  (∀ t, homotopyEquivalences C (a t)) →
    homotopyEquivalences C (Limits.Sigma.map a))

/- The fixed-shape and aggregate finite-coproduct stability interfaces. -/
#check homotopyEquivalences.coproducts.ofFiniteShape
#check @homotopyEquivalences.coproducts.finite

end Finite

end Coproducts

end CategoryTheory.SimplicialObject
