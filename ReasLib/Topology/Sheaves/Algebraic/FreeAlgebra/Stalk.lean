module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.Algebra.Category.CommRingCat.Under.FreeAlgebra
public import ReasLib.CategoryTheory.Sites.AlgebraicSheaf.FreeAlgebra
public import ReasLib.Topology.Sheaves.Stalks.Filtered
public import ReasLib.Topology.Sheaves.Stalks.Sheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of free commutative algebra sheaves

This file constructs the canonical forward comparison from the free commutative algebra on
stalks to the stalk of the corresponding free commutative algebra sheaf.  The construction first
uses the free-ring adjunction, then adjoins a base ring through `Under.costar`.  In particular, the
comparison data does not select an isomorphism from an existence theorem.

The inverse comparisons are constructed as well.  For the free ring, the stalk of the sheafified
presheaf `U ↦ ℤ[E(U)]` is first identified with the presheaf stalk by the explicit
`TopCat.Presheaf.SheafificationStalk.comparisonInv`, and the free-ring maps `ℤ[E(U)] → ℤ[Eₓ]`
induced by the germ maps are then descended through the stalk colimit by `colimit.post`.  For the
free algebra, the stalk of the sheaf coproduct `A ⨿ ℤ[E]` is mapped out of through the
stalk--skyscraper adjunction, using the base map on `A` and the free-ring inverse on `ℤ[E]`.
The invertibility instances are derived from these explicit isomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

namespace FreeCommRing

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]

namespace Stalk

/-- The stalk of the free commutative ring sheaf. -/
noncomputable abbrev sheaf (E : X.Sheaf (Type u)) (x : X) : CommRingCat.{u} :=
  TopCat.Presheaf.stalk (CategoryTheory.Sheaf.FreeCommRing.obj E).obj x

/-- The generator map on stalks, with the target identified with the underlying set of the
commutative-ring stalk. -/
noncomputable def generator (E : X.Sheaf (Type u)) (x : X) :
    E.presheaf.stalk x ⟶ (CategoryTheory.forget CommRingCat.{u}).obj (sheaf E x) :=
  (TopCat.Presheaf.stalkFunctor (Type u) x).map
      (CategoryTheory.Sheaf.FreeCommRing.generator E).hom ≫
    (TopCat.Presheaf.stalkCompIso x (CategoryTheory.forget CommRingCat.{u})
      (CategoryTheory.Sheaf.FreeCommRing.obj E).obj).inv

/-- The canonical forward comparison from the free commutative ring on the stalk of the
generators to the stalk of the free commutative ring sheaf. -/
@[stacks 0D09 "free-ring stalk comparison"]
noncomputable def comparison (E : X.Sheaf (Type u)) (x : X) :
    CommRingCat.free.obj (E.presheaf.stalk x) ⟶ sheaf E x :=
  (CommRingCat.adj.homEquiv _ _).symm (generator E x)

/-- The free-ring stalk comparison sends a polynomial generator to the corresponding stalk
generator. -/
@[stacks 0D09 "free-ring stalk comparison on generators"]
theorem comparison_generator (E : X.Sheaf (Type u)) (x : X)
    (e : E.presheaf.stalk x) :
    comparison E x ((CommRingCat.adj.unit.app (E.presheaf.stalk x)) e) =
      generator E x e := sorry

/-- The explicit inverse of the free-ring stalk comparison: the stalk of the sheafified
presheaf `U ↦ ℤ[E(U)]` is identified with the presheaf stalk, and the free-ring maps induced by
the germs `E(U) → Eₓ` are descended through the stalk colimit. -/
@[stacks 0D09 "inverse free-ring stalk comparison"]
noncomputable def comparisonInv (E : X.Sheaf (Type u)) (x : X) :
    sheaf E x ⟶ CommRingCat.free.obj (E.presheaf.stalk x) :=
  TopCat.Presheaf.SheafificationStalk.comparisonInv (E.presheaf ⋙ CommRingCat.free) x ≫
    colimit.post ((OpenNhds.inclusion x).op ⋙ E.presheaf) CommRingCat.free

/-- The inverse free-ring stalk comparison sends the germ of the image of `ℤ[E(U)]` in the
sheafification to the free-ring map induced by the germ `E(U) → Eₓ`. -/
@[reassoc, stacks 0D09 "inverse free-ring stalk comparison on germs"]
theorem toSheafify_germ_comparisonInv (E : X.Sheaf (Type u)) (x : X)
    (U : Opens X) (hx : x ∈ U) :
    (toSheafify (Opens.grothendieckTopology X) (E.presheaf ⋙ CommRingCat.free)).app
          (Opposite.op U) ≫
        TopCat.Presheaf.germ (CategoryTheory.Sheaf.FreeCommRing.obj E).obj U x hx ≫
          comparisonInv E x =
      CommRingCat.free.map (E.presheaf.germ U x hx) := sorry

/-- The free-ring stalk comparison followed by its named inverse is the identity. -/
@[simp, stacks 0D09 "free-ring stalk comparison forward-inverse law"]
theorem comparison_comp_comparisonInv (E : X.Sheaf (Type u)) (x : X) :
    comparison E x ≫ comparisonInv E x = 𝟙 _ := sorry

/-- The named inverse followed by the free-ring stalk comparison is the identity. -/
@[simp, stacks 0D09 "free-ring stalk comparison inverse-forward law"]
theorem comparisonInv_comp_comparison (E : X.Sheaf (Type u)) (x : X) :
    comparisonInv E x ≫ comparison E x = 𝟙 _ := sorry

/-- The free-ring stalk comparison as a literal isomorphism with an explicit inverse. -/
@[stacks 0D09 "free-ring stalk comparison isomorphism"]
noncomputable def comparisonIso (E : X.Sheaf (Type u)) (x : X) :
    CommRingCat.free.obj (E.presheaf.stalk x) ≅ sheaf E x where
  hom := comparison E x
  inv := comparisonInv E x
  hom_inv_id := comparison_comp_comparisonInv E x
  inv_hom_id := comparisonInv_comp_comparison E x

/-- The forward map of the free-ring stalk comparison isomorphism is `comparison`. -/
@[simp, stacks 0D09 "free-ring stalk comparison isomorphism hom"]
theorem comparisonIso_hom (E : X.Sheaf (Type u)) (x : X) :
    (comparisonIso E x).hom = comparison E x := rfl

/-- The inverse map of the free-ring stalk comparison isomorphism is `comparisonInv`. -/
@[simp, stacks 0D09 "free-ring stalk comparison isomorphism inverse"]
theorem comparisonIso_inv (E : X.Sheaf (Type u)) (x : X) :
    (comparisonIso E x).inv = comparisonInv E x := rfl

/-- The canonical free-ring stalk comparison is an isomorphism. -/
@[stacks 0D09 "free-ring stalk comparison is an isomorphism", instance]
instance comparison_isIso (E : X.Sheaf (Type u)) (x : X) :
    IsIso (comparison E x) :=
  (comparisonIso E x).isIso_hom

/-- The explicit inverse of the free-ring stalk comparison is itself an isomorphism. -/
@[stacks 0D09 "inverse free-ring stalk comparison is an isomorphism", instance]
instance comparisonInv_isIso (E : X.Sheaf (Type u)) (x : X) :
    IsIso (comparisonInv E x) :=
  (comparisonIso E x).isIso_inv

end Stalk

end FreeCommRing

namespace FreeAlgebra

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]

namespace Stalk

/-- The free commutative algebra over the stalk ring `A_x` generated by the stalk `E_x`. -/
noncomputable abbrev algebraic
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    Under (A.presheaf.stalk x) :=
  CommRingCat.Under.FreeAlgebra.algebraic
    (A.presheaf.stalk x) (E.presheaf.stalk x)

/-- The stalk of the free algebra sheaf, regarded as an algebra over `A_x`. -/
noncomputable abbrev sheaf
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    Under (A.presheaf.stalk x) :=
  Under.mk ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
    (CategoryTheory.Sheaf.FreeAlgebra.base A E).hom)

/-- The multivariable-polynomial model of the free algebra over `Aₓ` on the stalk `Eₓ`. -/
@[stacks 0D09 "polynomial model of the free-algebra stalk"]
noncomputable abbrev polynomial
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    Under (A.presheaf.stalk x) :=
  CommRingCat.Under.FreeAlgebra.polynomial
    (A.presheaf.stalk x) (E.presheaf.stalk x)

/-- The generator map of the free algebra over the stalk ring. -/
noncomputable def generator
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    E.presheaf.stalk x ⟶
      (CategoryTheory.forget CommRingCat.{u}).obj (algebraic A E x).right :=
  CommRingCat.Under.FreeAlgebra.generator
    (A.presheaf.stalk x) (E := E.presheaf.stalk x)

/-- The generator map obtained by taking the stalk of the free-algebra sheaf generator. -/
noncomputable def sheafGenerator
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    E.presheaf.stalk x ⟶
      (CategoryTheory.forget CommRingCat.{u}).obj (sheaf A E x).right :=
  (TopCat.Presheaf.stalkFunctor (Type u) x).map
      (CategoryTheory.Sheaf.FreeAlgebra.generator A E).hom ≫
    (TopCat.Presheaf.stalkCompIso x (CategoryTheory.forget CommRingCat.{u})
      (CategoryTheory.Sheaf.FreeAlgebra.underlying A E).obj).inv

/-- The free-algebra comparison, bundled as a morphism under the base stalk ring. -/
@[stacks 0D09 "free-algebra stalk comparison under the base"]
noncomputable def comparisonUnder
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    algebraic A E x ⟶ sheaf A E x :=
  ((Under.costarAdjForget (A.presheaf.stalk x)).homEquiv _ _).symm
    (TopCat.Sheaf.FreeCommRing.Stalk.comparison E x ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (CategoryTheory.Sheaf.FreeAlgebra.freeMap A E).hom)

/-- The canonical forward comparison from the free algebra on stalks to the stalk of the free
algebra sheaf. -/
@[stacks 0D09 "free-algebra stalk comparison"]
noncomputable abbrev comparison
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    (algebraic A E x).right ⟶ (sheaf A E x).right :=
  (comparisonUnder A E x).right

/-- The free-algebra stalk comparison is compatible with the structural maps from the base stalk
ring. -/
@[stacks 0D09 "free-algebra stalk comparison on the base"]
theorem comparison_base
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    (algebraic A E x).hom ≫ comparison A E x = (sheaf A E x).hom := sorry

/-- The free-algebra stalk comparison sends each algebraic generator to the stalk of the
corresponding sheaf generator. -/
@[stacks 0D09 "free-algebra stalk comparison on generators"]
theorem comparison_generator
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X)
    (e : E.presheaf.stalk x) :
    comparison A E x (generator A E x e) = sheafGenerator A E x e := sorry

/-- The generator assignment induced on stalks by a generator assignment of sheaves. -/
noncomputable def assignment
    {A : X.Sheaf CommRingCat.{u}} (B : Under A) (E : X.Sheaf (Type u))
    (assign : E ⟶
      (CategoryTheory.sheafForget (Opens.grothendieckTopology X)).obj B.right)
    (x : X) :
    E.presheaf.stalk x ⟶
      (CategoryTheory.forget CommRingCat.{u}).obj (B.right.presheaf.stalk x) :=
  (TopCat.Presheaf.stalkFunctor (Type u) x).map assign.hom ≫
    (TopCat.Presheaf.stalkCompIso x (CategoryTheory.forget CommRingCat.{u})
      B.right.presheaf).inv

/-- Evaluation of the free algebra on stalks at the induced stalk generator assignment. -/
noncomputable def evaluation
    {A : X.Sheaf CommRingCat.{u}} (B : Under A) (E : X.Sheaf (Type u))
    (assign : E ⟶
      (CategoryTheory.sheafForget (Opens.grothendieckTopology X)).obj B.right)
    (x : X) :
    algebraic A E x ⟶
      Under.mk ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map B.hom.hom) :=
  ((Under.costarAdjForget (A.presheaf.stalk x)).homEquiv _ _).symm
    ((CommRingCat.adj.homEquiv _ _).symm (assignment B E assign x))

/-- The free-algebra stalk comparison commutes with evaluation at every sheaf-level generator
assignment. -/
@[stacks 0D09 "free-algebra stalk comparison and evaluation"]
theorem comparison_evaluation
    {A : X.Sheaf CommRingCat.{u}} (B : Under A) (E : X.Sheaf (Type u))
    (assign : E ⟶
      (CategoryTheory.sheafForget (Opens.grothendieckTopology X)).obj B.right)
    (x : X) :
    comparison A E x ≫
        (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
          (CategoryTheory.Sheaf.FreeAlgebra.evaluation B E assign).right.hom =
      (evaluation B E assign x).right := sorry

/-- The map from the free algebra sheaf `A ⨿ ℤ[E]` to the skyscraper sheaf at `x` with value
`Aₓ[Eₓ]`, given on `A` by the structural map of `Aₓ[Eₓ]` and on `ℤ[E]` by the inverse free-ring
stalk comparison followed by the inclusion `ℤ[Eₓ] → Aₓ[Eₓ]`, both transposed along the
stalk--skyscraper adjunction. -/
noncomputable def toSkyscraper
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    CategoryTheory.Sheaf.FreeAlgebra.underlying A E ⟶
      Skyscraper.atPoint x (algebraic A E x).right :=
  coprod.desc
    ((Skyscraper.stalkAdjunction x).homEquiv A (algebraic A E x).right
      (algebraic A E x).hom)
    ((Skyscraper.stalkAdjunction x).homEquiv (CategoryTheory.Sheaf.FreeCommRing.obj E)
      (algebraic A E x).right
      (TopCat.Sheaf.FreeCommRing.Stalk.comparisonInv E x ≫
        (Under.costarAdjForget (A.presheaf.stalk x)).unit.app
          (CommRingCat.free.obj (E.presheaf.stalk x))))

/-- The explicit inverse of the underlying free-algebra stalk comparison, obtained by transposing
`toSkyscraper` along the stalk--skyscraper adjunction. -/
@[stacks 0D09 "inverse free-algebra stalk comparison"]
noncomputable def comparisonInv
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    (sheaf A E x).right ⟶ (algebraic A E x).right :=
  ((Skyscraper.stalkAdjunction x).homEquiv _ _).symm (toSkyscraper A E x)

/-- The inverse free-algebra stalk comparison is compatible with the structural maps from the
base stalk ring. -/
@[stacks 0D09 "inverse free-algebra stalk comparison on the base"]
theorem comparisonInv_base
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    (sheaf A E x).hom ≫ comparisonInv A E x = (algebraic A E x).hom := sorry

/-- The inverse free-algebra stalk comparison sends the stalk of each sheaf generator to the
corresponding algebraic generator. -/
@[stacks 0D09 "inverse free-algebra stalk comparison on generators"]
theorem comparisonInv_sheafGenerator
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X)
    (e : E.presheaf.stalk x) :
    comparisonInv A E x (sheafGenerator A E x e) = generator A E x e := sorry

/-- The explicit inverse of the free-algebra stalk comparison under the base stalk ring. -/
@[stacks 0D09 "inverse free-algebra stalk comparison under the base"]
noncomputable def comparisonUnderInv
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    sheaf A E x ⟶ algebraic A E x :=
  Under.homMk (comparisonInv A E x) (comparisonInv_base A E x)

/-- The underlying ring map of the under-base inverse is `comparisonInv`. -/
@[simp, stacks 0D09 "inverse free-algebra stalk comparison under the base on rings"]
theorem comparisonUnderInv_right
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    (comparisonUnderInv A E x).right = comparisonInv A E x := rfl

/-- The free-algebra stalk comparison under the base followed by its named inverse is the
identity. -/
@[simp, stacks 0D09 "free-algebra stalk comparison under-base forward-inverse law"]
theorem comparisonUnder_comp_comparisonUnderInv
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    comparisonUnder A E x ≫ comparisonUnderInv A E x = 𝟙 _ := sorry

/-- The named inverse of the free-algebra stalk comparison under the base followed by the
comparison is the identity. -/
@[simp, stacks 0D09 "free-algebra stalk comparison under-base inverse-forward law"]
theorem comparisonUnderInv_comp_comparisonUnder
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    comparisonUnderInv A E x ≫ comparisonUnder A E x = 𝟙 _ := sorry

/-- The free-algebra stalk comparison under the base as a literal isomorphism with an explicit
inverse. -/
@[stacks 0D09 "free-algebra stalk comparison under-base isomorphism"]
noncomputable def comparisonUnderIso
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    algebraic A E x ≅ sheaf A E x where
  hom := comparisonUnder A E x
  inv := comparisonUnderInv A E x
  hom_inv_id := comparisonUnder_comp_comparisonUnderInv A E x
  inv_hom_id := comparisonUnderInv_comp_comparisonUnder A E x

/-- The forward map of the under-base comparison isomorphism is `comparisonUnder`. -/
@[simp, stacks 0D09 "free-algebra stalk under-base comparison isomorphism hom"]
theorem comparisonUnderIso_hom
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    (comparisonUnderIso A E x).hom = comparisonUnder A E x := rfl

/-- The inverse map of the under-base comparison isomorphism is `comparisonUnderInv`. -/
@[simp, stacks 0D09 "free-algebra stalk under-base comparison isomorphism inverse"]
theorem comparisonUnderIso_inv
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    (comparisonUnderIso A E x).inv = comparisonUnderInv A E x := rfl

/-- The comparison is an isomorphism in the category under the base stalk ring. -/
@[stacks 0D09 "free-algebra stalk comparison under the base is an isomorphism", instance]
instance comparisonUnder_isIso
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    IsIso (comparisonUnder A E x) :=
  (comparisonUnderIso A E x).isIso_hom

/-- The explicit inverse under the base stalk ring is an isomorphism. -/
@[stacks 0D09 "inverse free-algebra stalk comparison under the base is an isomorphism", instance]
instance comparisonUnderInv_isIso
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    IsIso (comparisonUnderInv A E x) :=
  (comparisonUnderIso A E x).isIso_inv

/-- The free-algebra stalk comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 0D09 "free-algebra stalk comparison forward-inverse law"]
theorem comparison_comp_comparisonInv
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    comparison A E x ≫ comparisonInv A E x = 𝟙 _ := sorry

/-- The explicit inverse followed by the free-algebra stalk comparison is the identity. -/
@[simp, stacks 0D09 "free-algebra stalk comparison inverse-forward law"]
theorem comparisonInv_comp_comparison
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    comparisonInv A E x ≫ comparison A E x = 𝟙 _ := sorry

/-- The free-algebra stalk comparison on underlying rings as a literal isomorphism. -/
@[stacks 0D09 "free-algebra stalk comparison isomorphism"]
noncomputable def comparisonIso
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    (algebraic A E x).right ≅ (sheaf A E x).right where
  hom := comparison A E x
  inv := comparisonInv A E x
  hom_inv_id := comparison_comp_comparisonInv A E x
  inv_hom_id := comparisonInv_comp_comparison A E x

/-- The forward map of the free-algebra stalk comparison isomorphism is `comparison`. -/
@[simp, stacks 0D09 "free-algebra stalk comparison isomorphism hom"]
theorem comparisonIso_hom
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    (comparisonIso A E x).hom = comparison A E x := rfl

/-- The inverse map of the free-algebra stalk comparison isomorphism is `comparisonInv`. -/
@[simp, stacks 0D09 "free-algebra stalk comparison isomorphism inverse"]
theorem comparisonIso_inv
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    (comparisonIso A E x).inv = comparisonInv A E x := rfl

/-- The canonical free-algebra stalk comparison is an isomorphism. -/
@[stacks 0D09 "free-algebra stalk comparison is an isomorphism", instance]
instance comparison_isIso
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    IsIso (comparison A E x) :=
  (comparisonIso A E x).isIso_hom

/-- The explicit inverse of the underlying free-algebra stalk comparison is an isomorphism. -/
@[stacks 0D09 "inverse free-algebra stalk comparison is an isomorphism", instance]
instance comparisonInv_isIso
    (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    IsIso (comparisonInv A E x) :=
  (comparisonIso A E x).isIso_inv

/-- The stalk of the free-algebra sheaf is canonically isomorphic, under the base stalk ring, to
the multivariable-polynomial model. -/
@[stacks 0D09 "free-algebra sheaf stalk polynomial identification"]
noncomputable def sheafPolynomialIso
  (A : X.Sheaf CommRingCat.{u}) (E : X.Sheaf (Type u)) (x : X) :
    sheaf A E x ≅ polynomial A E x :=
  (comparisonUnderIso A E x).symm ≪≫
    CommRingCat.Under.FreeAlgebra.polynomialIso
      (A.presheaf.stalk x) (E.presheaf.stalk x)

end Stalk

end FreeAlgebra

end TopCat.Sheaf
