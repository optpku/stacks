module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Factorization
import StacksCheckRecall

/-!
# Open-then-closed factorizations of quasi-compact immersions

A quasi-compact immersion of algebraic spaces over a scheme factors as an
open immersion followed by a closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsImmersion

/- Lemma 67.12.6: Let `S` be a scheme. Let `f : Z ⟶ X` be an immersion of
algebraic spaces over `S`. Assume `f` is quasi-compact. There exists a
factorization `Z ⟶ Zbar ⟶ X` where `Z ⟶ Zbar` is an open immersion and
`Zbar ⟶ X` is a closed immersion. -/
@[stacks 081U] #check
  (AlgebraicGeometry.AlgebraicSpace.IsImmersion.exists_openImmersion_closedImmersion_factorization :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (f : Z ⟶ X)
      [IsImmersion f] [QuasiCompact f],
    ∃ (Zbar : AlgebraicSpace S) (j : Z ⟶ Zbar) (i : Zbar ⟶ X),
      IsOpenImmersion j ∧ IsClosedImmersion i ∧ j ≫ i = f)

/- A quasi-compact morphism of algebraic spaces is an immersion if and only if
it factors as an open immersion followed by a closed immersion. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsImmersion.iff_exists_of_quasiCompact :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (f : Z ⟶ X) [QuasiCompact f],
    IsImmersion f ↔
      ∃ (Zbar : AlgebraicSpace S) (j : Z ⟶ Zbar) (i : Zbar ⟶ X),
        IsOpenImmersion j ∧ IsClosedImmersion i ∧ j ≫ i = f)

end IsImmersion

end AlgebraicGeometry.AlgebraicSpace
