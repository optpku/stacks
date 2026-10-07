module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension.LocallyAlgebraic

@[expose] public section

universe u

/- Lemma 33.20.3 (1): the underlying topological space of a locally algebraic scheme over a
field is catenary. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.instCatenarySpaceOfLocallyAlgebraic :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X],
      TopologicalSpace.CatenarySpace X.left)

/- Lemma 33.20.3 (2): at a closed point, local topological dimension equals the Krull dimension
of the local ring. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.topologicalKrullDimAt_eq_ringKrullDim_stalk_of_isClosed :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X] (x : X.left),
      IsClosed ({x} : Set X.left) →
        topologicalKrullDimAt x =
          ringKrullDim (AlgebraicGeometry.SchemeOverField.stalkRing X x))

/- Lemma 33.20.3 (3a): every nonempty open of an irreducible locally algebraic scheme has the
same dimension as the whole scheme. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.topologicalKrullDim_open_eq_of_irreducible :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X] [IrreducibleSpace X.left]
      (U : X.left.Opens),
      Set.Nonempty (U : Set X.left) →
        topologicalKrullDim U = topologicalKrullDim X.left)

/- Lemma 33.20.3 (3b): every point of an irreducible locally algebraic scheme has local
dimension equal to the global dimension. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X] [IrreducibleSpace X.left]
      (x : X.left),
      topologicalKrullDim X.left = topologicalKrullDimAt x)

/- Lemma 33.20.3 (4a): every chain of irreducible closed subsets is contained in a maximal
chain. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.exists_maxChain_irreducibleCloseds :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X] [IrreducibleSpace X.left]
      (s : Set (TopologicalSpace.IrreducibleCloseds X.left)),
      IsChain (· ≤ ·) s →
        ∃ t : Set (TopologicalSpace.IrreducibleCloseds X.left),
          IsMaxChain (· ≤ ·) t ∧ s ⊆ t)

/- Lemma 33.20.3 (4b): every maximal chain of irreducible closed subsets of an irreducible
locally algebraic scheme has length equal to its dimension. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.maxChainIrreducibleCloseds_encard :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X] [IrreducibleSpace X.left]
      (s : Set (TopologicalSpace.IrreducibleCloseds X.left)),
      IsMaxChain (· ≤ ·) s →
        ((s.encard : ℕ∞) : WithBot ℕ∞) = topologicalKrullDim X.left + 1)

/- Lemma 33.20.3 (5a): local dimension is the attained maximum of the dimensions of the
irreducible components through the point. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.isGreatest_topologicalKrullDim_irreducibleComponents_through :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X] (x : X.left),
      IsGreatest
        {d : WithBot ℕ∞ |
          ∃ Z : irreducibleComponents X.left,
            x ∈ (Z : Set X.left) ∧ d = topologicalKrullDim Z}
        (topologicalKrullDimAt x))

/- Lemma 33.20.3 (5b): local dimension is the attained minimum of the dimensions of the local
rings at closed specializations. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.isLeast_ringKrullDim_stalk_closedSpecializations :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X] (x : X.left),
      IsLeast
        {d : WithBot ℕ∞ |
          ∃ x' : {x' : X.left // IsClosed ({x'} : Set X.left)},
            Specializes x x' ∧
              d = ringKrullDim (AlgebraicGeometry.SchemeOverField.stalkRing X x')}
        (topologicalKrullDimAt x))

/- Lemma 33.20.3 (6): on an irreducible locally algebraic scheme, the global dimension is the
base-field transcendence degree at its generic point. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.topologicalKrullDim_eq_baseFieldTrdegAt_of_mem_genericPoints :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X] [IrreducibleSpace X.left]
      (x : X.left),
      x ∈ genericPoints X.left →
        topologicalKrullDim X.left =
          (AlgebraicGeometry.SchemeOverField.baseFieldTrdegAt X x : WithBot ℕ∞))

/- Lemma 33.20.3 (7): base-field transcendence degree drops by one along an immediate
specialization. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.baseFieldTrdegAt_eq_add_one_of_immediateSpecialization :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X] {x x' : X.left},
      IsImmediateSpecialization x x' →
        AlgebraicGeometry.SchemeOverField.baseFieldTrdegAt X x =
          AlgebraicGeometry.SchemeOverField.baseFieldTrdegAt X x' + 1)

/- Lemma 33.20.3 (8): global dimension is the supremum of the base-field transcendence degrees
at the generic points of the irreducible components. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.topologicalKrullDim_eq_iSup_baseFieldTrdegAt_genericPoints :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X],
      topologicalKrullDim X.left =
        ⨆ η : genericPoints X.left,
          (AlgebraicGeometry.SchemeOverField.baseFieldTrdegAt X η : WithBot ℕ∞))

/- Lemma 33.20.3 (9a): local dimension is monotone along specialization. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.topologicalKrullDimAt_le_of_nontrivialSpecialization :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X] {x x' : X.left},
      Specializes x x' → x ≠ x' →
        topologicalKrullDimAt x ≤ topologicalKrullDimAt x')

/- Lemma 33.20.3 (9b): Krull dimension of local rings strictly increases along a nontrivial
specialization. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.ringKrullDim_stalk_lt_of_nontrivialSpecialization :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X] {x x' : X.left},
      Specializes x x' → x ≠ x' →
        ringKrullDim (AlgebraicGeometry.SchemeOverField.stalkRing X x) <
          ringKrullDim (AlgebraicGeometry.SchemeOverField.stalkRing X x'))

/- Lemma 33.20.3 (9c): base-field transcendence degree strictly decreases along a nontrivial
specialization. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.baseFieldTrdegAt_gt_of_nontrivialSpecialization :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X] {x x' : X.left},
      Specializes x x' → x ≠ x' →
        AlgebraicGeometry.SchemeOverField.baseFieldTrdegAt X x >
          AlgebraicGeometry.SchemeOverField.baseFieldTrdegAt X x')

/- Lemma 33.20.3 (9d): every maximal chain in a specialization interval has length equal to the
difference of the endpoint base-field transcendence degrees. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.maxChainSpecializationInterval_encard :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X] {x x' : X.left},
      Specializes x x' → x ≠ x' →
        ∀ (s : Set
          (Set.Icc (Specialization.toEquiv x') (Specialization.toEquiv x))),
          IsMaxChain (· ≤ ·) s →
            s.encard =
              AlgebraicGeometry.SchemeOverField.baseFieldTrdegAt X x -
                AlgebraicGeometry.SchemeOverField.baseFieldTrdegAt X x' + 1)

/- Lemma 33.20.3 (10): local dimension is the sum of base-field transcendence degree and the
Krull dimension of the local ring. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.topologicalKrullDimAt_eq_baseFieldTrdegAt_add_ringKrullDim_stalk :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X] (x : X.left),
      topologicalKrullDimAt x =
        (AlgebraicGeometry.SchemeOverField.baseFieldTrdegAt X x : WithBot ℕ∞) +
          ringKrullDim (AlgebraicGeometry.SchemeOverField.stalkRing X x))

/- Lemma 33.20.3 (11a): along an immediate specialization in an irreducible locally algebraic
scheme, the Krull dimension of the local ring increases by one. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.ringKrullDim_stalk_eq_add_one_of_immediateSpecialization_of_irreducible :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X] [IrreducibleSpace X.left]
      {x x' : X.left},
      IsImmediateSpecialization x x' →
        ringKrullDim (AlgebraicGeometry.SchemeOverField.stalkRing X x') =
          ringKrullDim (AlgebraicGeometry.SchemeOverField.stalkRing X x) + 1)

/- Lemma 33.20.3 (11b): along an immediate specialization in an equidimensional locally
algebraic scheme, the Krull dimension of the local ring increases by one. -/
@[stacks 0A21] #check
  (AlgebraicGeometry.SchemeOverField.ringKrullDim_stalk_succ_of_equidimensional :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.LocallyAlgebraic X]
      [TopologicalSpace.EquidimensionalSpace X.left] {x x' : X.left},
      IsImmediateSpecialization x x' →
        ringKrullDim (AlgebraicGeometry.SchemeOverField.stalkRing X x') =
          ringKrullDim (AlgebraicGeometry.SchemeOverField.stalkRing X x) + 1)
