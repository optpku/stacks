module

public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType

/-!
# Topologically finite type algebras

An `R`-algebra `S` is topologically of finite type with respect to an ideal `I`
when it is `I`-adically complete and the special fiber `S ⧸ I S` is of finite
type over `R ⧸ I`. The category `CommAlgCat.TopologicallyFiniteType` is the
corresponding full subcategory of `CommAlgCat`.
-/

@[expose] public section

universe v u

#check (CommAlgCat.TopologicallyFiniteType.{v, u} :
  ∀ (R : Type u) [CommRing R], Ideal R → Type (max u (v + 1)))
