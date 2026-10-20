module

public import ReasLib.Algebra.PolynomialSite.Resolution
import StacksCheckRecall

/-!
# Polynomial simplicial resolutions

The canonical resolution predicate and its constructions are available from the polynomial-site
resolution owner.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SimplicialObject

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {P : SimplicialObject (CommAlgCat.{u} A)}
variable (ε : P ⟶ (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))

/- Remark 92.5.5 (Resolutions) (1): an augmentation is a resolution when its terms are
polynomial algebras and its underlying simplicial-set map is a trivial Kan fibration. -/
@[stacks 08QI]
#check (Algebra.PolynomialSite.IsResolution ε : Prop)
