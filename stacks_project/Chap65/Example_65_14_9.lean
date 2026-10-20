module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.PointSpace
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace.InfiniteProduct

universe u

/- Example 65.14.9 (1): the projections `pr_n : A → k` define open immersions `f_n : S ⟶ U`. -/
@[stacks 02Z8]
#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.instIsOpenImmersion_immersion :
    ∀ (k : Type u) [Field k] (n : ℕ), IsOpenImmersion (immersion k n))

/- Example 65.14.9 (2): the projections `pr_n : A → k` define closed immersions `f_n : S ⟶ U`. -/
@[stacks 02Z8]
#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.instIsClosedImmersion_immersion :
    ∀ (k : Type u) [Field k] (n : ℕ), IsClosedImmersion (immersion k n))

/- Example 65.14.9 (3): the morphism `j : R ⟶ U ×_S U` is an étale equivalence relation. -/
@[stacks 02Z8]
#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.instIsEtaleEquivalenceRelation_preRelation :
    ∀ (k : Type u) [Field k], (preRelation k).IsEtaleEquivalenceRelation)

/- Example 65.14.9 (4): the quotient `X = U / R` is the fppf sheaf of the étale equivalence
relation, an algebraic space over `S` via `uliftYoneda`, with section induced by `f_0`. -/
@[stacks 02Z8]
#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.sheafOfPoints :
    ∀ (k : Type u) [Field k],
      Sheaf (Scheme.fppfTopology.over (base k)) (Type (u + 1)))

#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.sheafOfPoints_spec :
    ∀ (k : Type u) [Field k],
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k).hom ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k).hom ∧
          uliftYoneda.{u + 1}.relativelyRepresentable (diag (sheafOfPoints k).obj))

#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.atlas_etale :
    ∀ (k : Type u) [Field k],
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k).hom)

#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.atlas_locallySurjective :
    ∀ (k : Type u) [Field k],
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k).hom)

#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.representableDiagonal_sheafOfPoints :
    ∀ (k : Type u) [Field k],
      uliftYoneda.{u + 1}.relativelyRepresentable (diag (sheafOfPoints k).obj))

#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.sectionHom :
    ∀ (k : Type u) [Field k],
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (Over.mk (𝟙 (base k))) ⟶
        sheafOfPoints k)

/- Example 65.14.9 (5): if `k` is finite with `q` elements, then every `x : A` satisfies
`x ^ q = x`. -/
@[stacks 02Z8]
#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.pow_card : ∀ (k : Type u) [Field k] [Fintype k] (x : ℕ → k), x ^ Fintype.card k = x)

/- Example 65.14.9 (6): every residue field of `A` is isomorphic to `k`. -/
@[stacks 02Z8]
#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.nonempty_residueField_ringEquiv :
    ∀ (k : Type u) [Field k] [Fintype k] (x : (cover k).left),
      Nonempty ((cover k).left.residueField x ≃+* k))

/- Example 65.14.9 (7): all points of `U` are closed. -/
@[stacks 02Z8]
#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.mem_closedPoints_cover :
    ∀ (k : Type u) [Field k] [Fintype k] (x : (cover k).left),
      x ∈ closedPoints (cover k).left)

/- Example 65.14.9 (8): the topology on `|U|` is not the discrete topology. -/
@[stacks 02Z8]
#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.not_discreteTopology_cover :
    ∀ (k : Type u) [Field k] [Fintype k], ¬ DiscreteTopology (cover k).left)

/- Example 65.14.9 (9): the points `u_n` corresponding to `f_n` are open, hence isolated. -/
@[stacks 02Z8]
#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.isOpen_singleton_openPoint :
    ∀ (k : Type u) [Field k] [Fintype k] (n : ℕ), IsOpen {openPoint k n})

/- Example 65.14.9 (10): `|U|` has points other than the open points `u_n`, since `U` is
quasi-compact and the proper finite-support ideal is contained in a maximal ideal. -/
@[stacks 02Z8]
#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.exists_point_not_openPoint :
    ∀ (k : Type u) [Field k] [Fintype k], ∃ x : (cover k).left, ∀ n : ℕ, x ≠ openPoint k n)

/- Example 65.14.9 (11): every element of `A` is of the form `x = u * e` with `u` a unit and
`e` an idempotent. -/
@[stacks 02Z8]
#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.exists_isUnit_mul_isIdempotentElem :
    ∀ (k : Type u) [Field k] [Fintype k] (x : ℕ → k),
      ∃ (u e : ℕ → k), IsUnit u ∧ IsIdempotentElem e ∧ x = u * e)

/- Example 65.14.9 (12): the topology on `|U|` is totally disconnected. -/
@[stacks 02Z8]
#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.instTotallyDisconnectedSpace_cover :
    ∀ (k : Type u) [Field k] [Fintype k], TotallyDisconnectedSpace (cover k).left)

/- Example 65.14.9 (13): the set `{u_n}` is dense in `|U|`. -/
@[stacks 02Z8]
#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.dense_range_openPoint :
    ∀ (k : Type u) [Field k] [Fintype k], Dense (Set.range (openPoint k)))

/- Example 65.14.9 (14): the map `|U| ⟶ |X|` is surjective and continuous; all open points
`u_n` map to the same point of `|X|`, and no other points are identified. -/
@[stacks 02Z8]
#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.quotientMap_surjective :
    ∀ (k : Type u) [Field k], Function.Surjective (quotientMap k))

#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.continuous_quotientMap :
    ∀ (k : Type u) [Field k], Continuous (quotientMap k))

#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.spaceRel_iff :
    ∀ (k : Type u) [Field k] [Fintype k] (x y : (cover k).left),
      spaceRel k x y ↔
        x = y ∨ (∃ n, x = openPoint k n) ∧ (∃ m, y = openPoint k m))

/- Example 65.14.9 (15): `|X|` is irreducible, `x_0` is a generic point of `|X|`, and `x_0` is
the image of a section `S ⟶ X`. -/
@[stacks 02Z8]
#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.instIrreducibleSpace_spacePoints :
    ∀ (k : Type u) [Field k] [Fintype k], IrreducibleSpace (spacePoints k))

#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.isGenericPoint_genericPoint :
    ∀ (k : Type u) [Field k] [Fintype k], IsGenericPoint (genericPoint k) Set.univ)

#check
  (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.genericPoint_eq_image_section :
    ∀ (k : Type u) [Field k] [Fintype k],
      sectionHom k =
          (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (immersionOver k 0) ≫
            atlas k ∧
        genericPoint k =
          quotientMap k ((immersionOver k 0).left (IsLocalRing.closedPoint k)))
