module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quotients of internally graded algebras

This leaf gives the canonical internal grading on a quotient by a homogeneous
ideal.  The degree-`i` quotient piece is the image of the source piece under
the quotient map; a homogeneous ideal is precisely what lets these pieces
form an internal direct-sum decomposition again. For a noncommutative source
ring, the ideal is required to be two-sided so that its ring quotient exists.
-/

@[expose] public section

open scoped DirectSum

universe u v w

namespace GradedAlgebra.Quotient

variable {ι : Type u}
variable {R : Type v} {A : Type w}
variable [CommSemiring R] [Ring A] [Algebra R A]
variable (𝒜 : ι → Submodule R A) (J : Ideal A) [J.IsTwoSided]

section Component

/-- The degree-`i` piece of the quotient by `J`, obtained by mapping the degree-`i`
piece of the source grading through `A → A ⧸ J`. -/
@[stacks 052N "homogeneous ideal quotient grading"]
noncomputable def grading (i : ι) : Submodule R (A ⧸ J) :=
  (𝒜 i).map (Ideal.Quotient.mkₐ R J).toLinearMap

/-- The quotient map restricted to the degree-`i` source piece. -/
@[stacks 052N "homogeneous ideal quotient component map"]
noncomputable def componentMap (i : ι) :
    𝒜 i →ₗ[R] grading 𝒜 J i :=
  LinearMap.codRestrict
    (grading 𝒜 J i)
    ((Ideal.Quotient.mkₐ R J).toLinearMap.domRestrict (𝒜 i))
    (fun x ↦ ⟨x, x.2, rfl⟩)

/-- The quotient class of a degree-`i` source element lies in the degree-`i`
quotient piece. -/
@[stacks 052N "homogeneous quotient class"]
theorem mk_mem_grading {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    Ideal.Quotient.mk J a ∈ grading 𝒜 J i := sorry

/-- Every element of a quotient degree piece has a representative in the
corresponding source degree piece. -/
@[stacks 052N "homogeneous quotient representative"]
theorem exists_rep_of_mem_grading {i : ι}
    (x : grading 𝒜 J i) :
    ∃ a : 𝒜 i, Ideal.Quotient.mk J (a : A) = x := sorry

/-- The component map has the expected quotient class after coercing out of
the target degree piece. -/
@[simp, stacks 052N "homogeneous quotient component value"]
theorem componentMap_apply (i : ι) (a : 𝒜 i) :
    (componentMap 𝒜 J i a : A ⧸ J) =
      Ideal.Quotient.mk J (a : A) := sorry

/-
API design: a mapped submodule is a range by construction, so surjectivity belongs beside
`componentMap`.  `componentLinearEquiv` then packages exactly the extra injectivity fact a caller
must prove; quotient applications should not rebuild image witnesses or duplicate the map.
-/

/-- The quotient component map is surjective onto its mapped degree piece. -/
@[stacks 052N "homogeneous quotient component surjectivity"]
theorem componentMap_surjective (i : ι) :
    Function.Surjective (componentMap 𝒜 J i) := sorry

/-- An injective quotient component map identifies the source piece with its quotient image. -/
@[stacks 052N "homogeneous quotient component equivalence"]
noncomputable def componentLinearEquiv (i : ι)
    (h : Function.Injective (componentMap 𝒜 J i)) :
    𝒜 i ≃ₗ[R] grading 𝒜 J i :=
  LinearEquiv.ofBijective (componentMap 𝒜 J i)
    ⟨h, componentMap_surjective 𝒜 J i⟩

end Component

section Graded

variable [DecidableEq ι] [AddMonoid ι]
variable [GradedAlgebra 𝒜]

/-- The quotient class of `1` belongs to the degree-zero quotient piece. -/
@[stacks 052N "homogeneous quotient one membership"]
theorem one_mem_grading : (1 : A ⧸ J) ∈ grading 𝒜 J 0 := sorry

/-- Products of elements from quotient degree pieces have the expected degree. -/
@[stacks 052N "homogeneous quotient multiplication membership"]
theorem mul_mem_grading {i j : ι} {x y : A ⧸ J}
    (hx : x ∈ grading 𝒜 J i) (hy : y ∈ grading 𝒜 J j) :
    x * y ∈ grading 𝒜 J (i + j) := sorry

/-- The quotient pieces are multiplicatively graded even before the
homogeneity hypothesis needed for the internal direct-sum decomposition. -/
@[stacks 052N "homogeneous ideal quotient graded monoid"]
instance setLikeGradedMonoid :
    SetLike.GradedMonoid (grading 𝒜 J) where
  one_mem := one_mem_grading 𝒜 J
  mul_mem := fun _ _ _ _ hx hy => mul_mem_grading 𝒜 J hx hy

/-- The degreewise quotient maps preserve the degree-zero multiplicative
generator of the direct sum. -/
@[stacks 052N "homogeneous quotient direct-sum one"]
theorem directSumComponentMap_one :
    (DirectSum.lof R ι (fun i ↦ grading 𝒜 J i) 0)
      (componentMap 𝒜 J 0 ⟨1, SetLike.one_mem_graded 𝒜⟩) = 1 := sorry

/-- The degreewise quotient maps preserve multiplication of homogeneous
direct-sum generators. -/
@[stacks 052N "homogeneous quotient direct-sum multiplication"]
theorem directSumComponentMap_mul {i j : ι}
    (x : 𝒜 i) (y : 𝒜 j) :
    (DirectSum.lof R ι (fun k ↦ grading 𝒜 J k) (i + j))
      (componentMap 𝒜 J (i + j)
        ⟨x.1 * y.1, SetLike.mul_mem_graded x.2 y.2⟩) =
      (DirectSum.lof R ι (fun k ↦ grading 𝒜 J k) i)
        (componentMap 𝒜 J i x) *
        (DirectSum.lof R ι (fun k ↦ grading 𝒜 J k) j)
          (componentMap 𝒜 J j y) := sorry

/-- The algebra map from the direct sum of source pieces to the direct sum of
their quotient images, defined degreewise by `componentMap`. -/
@[stacks 052N "homogeneous ideal quotient direct-sum map"]
noncomputable def directSumAlgHom :
    (⨁ i, 𝒜 i) →ₐ[R] (⨁ i, grading 𝒜 J i) :=
  DirectSum.toAlgebra (R := R)
    (A := fun i ↦ 𝒜 i)
    (B := ⨁ i, grading 𝒜 J i)
    (fun i ↦
      (DirectSum.lof R ι (fun k ↦ grading 𝒜 J k) i).comp
        (componentMap 𝒜 J i))
    (directSumComponentMap_one 𝒜 J)
    (fun {_i _j} x y ↦ directSumComponentMap_mul 𝒜 J x y)

/-- Decompose an element of `A` and map each homogeneous component to the
corresponding quotient piece. -/
@[stacks 052N "homogeneous ideal quotient predecomposition"]
noncomputable def predecompose :
    A →ₗ[R] DirectSum ι (fun i ↦ grading 𝒜 J i) :=
  (DirectSum.lmap fun i ↦ componentMap 𝒜 J i).comp
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

/-- The algebraic version of `predecompose`, using the graded algebra
equivalence of the source. -/
@[stacks 052N "homogeneous ideal quotient algebraic predecomposition"]
noncomputable def predecomposeAlgHom :
    A →ₐ[R] (⨁ i, grading 𝒜 J i) :=
  (directSumAlgHom 𝒜 J).comp (DirectSum.decomposeAlgEquiv 𝒜).toAlgHom

/-- The algebraic and linear quotient predecompositions agree pointwise. -/
@[stacks 052N "homogeneous quotient predecomposition value"]
theorem predecomposeAlgHom_apply (a : A) :
    predecomposeAlgHom 𝒜 J a = predecompose 𝒜 J a := sorry

/-- A homogeneous source element maps under the quotient predecomposition to
the matching direct-sum summand. -/
@[stacks 052N "homogeneous quotient predecomposition component"]
theorem predecompose_eq_of_mem {i : ι} {a : A}
    (ha : a ∈ 𝒜 i) :
    predecompose 𝒜 J a =
      DirectSum.of (fun k ↦ grading 𝒜 J k) i
        ⟨Ideal.Quotient.mk J a, mk_mem_grading 𝒜 J ha⟩ := sorry

/-- A homogeneous ideal is killed by the componentwise quotient
predecomposition. -/
@[stacks 052N "homogeneous quotient predecomposition ideal kernel"]
theorem predecomposeAlgHom_eq_zero_of_mem
    (hJ : J.IsHomogeneous 𝒜) (a : A) (ha : a ∈ J) :
    predecomposeAlgHom 𝒜 J a = 0 := sorry

/-- The quotient predecomposition descended through a homogeneous ideal.  Its
computational map is explicit; only the proof that the ideal is annihilated is
used to justify the quotient lift. -/
@[stacks 052N "homogeneous ideal quotient decomposition map"]
noncomputable def decomposeAlgHom (hJ : J.IsHomogeneous 𝒜) :
    A ⧸ J →ₐ[R] (⨁ i, grading 𝒜 J i) :=
  Ideal.Quotient.liftₐ J
    (predecomposeAlgHom 𝒜 J)
    (predecomposeAlgHom_eq_zero_of_mem 𝒜 J hJ)

/-- The descended quotient decomposition agrees with the source
predecomposition after precomposing with the quotient map. -/
@[stacks 052N "homogeneous quotient decomposition quotient map"]
theorem decomposeAlgHom_comp_mk (hJ : J.IsHomogeneous 𝒜) :
    (decomposeAlgHom 𝒜 J hJ).comp (Ideal.Quotient.mkₐ R J) =
      predecomposeAlgHom 𝒜 J := sorry

/-- Recomposing the descended quotient decomposition is the identity on
`A ⧸ J`. -/
@[stacks 052N "homogeneous quotient decomposition right inverse"]
theorem decomposeAlgHom_right_inv (hJ : J.IsHomogeneous 𝒜) :
    (DirectSum.coeAlgHom (grading 𝒜 J)).comp (decomposeAlgHom 𝒜 J hJ) =
      AlgHom.id R (A ⧸ J) := sorry

/-- The descended quotient decomposition sends each quotient homogeneous
element to its matching direct-sum generator. -/
@[stacks 052N "homogeneous quotient decomposition component"]
theorem decomposeAlgHom_left_inv (hJ : J.IsHomogeneous 𝒜)
    (i : ι) (x : grading 𝒜 J i) :
    decomposeAlgHom 𝒜 J hJ (x : A ⧸ J) =
      DirectSum.of (fun k ↦ grading 𝒜 J k) i x := sorry

/-- The canonical graded-algebra structure on the quotient by a homogeneous
ideal.  This is an explicit owner rather than a global instance because the
chosen proof of homogeneity is an input. -/
@[reducible, stacks 052N "homogeneous ideal quotient graded algebra"]
noncomputable def gradedAlgebra (hJ : J.IsHomogeneous 𝒜) :
    GradedAlgebra (grading 𝒜 J) :=
  GradedAlgebra.ofAlgHom (grading 𝒜 J)
    (decomposeAlgHom 𝒜 J hJ)
    (decomposeAlgHom_right_inv 𝒜 J hJ)
    (decomposeAlgHom_left_inv 𝒜 J hJ)

/-- The direct-sum decomposition underlying the canonical quotient graded
algebra. -/
@[reducible, stacks 052N "homogeneous ideal quotient decomposition"]
noncomputable def decomposition (hJ : J.IsHomogeneous 𝒜) :
    DirectSum.Decomposition (grading 𝒜 J) :=
  GradedRing.toDecomposition (self := gradedAlgebra 𝒜 J hJ)

/-
API design: the general homogeneous-ideal constructors above remain the primary owners.  The only
principal specialization retained is the graded-algebra producer used by quotient inductions.  It
accepts Mathlib's existential `SetLike.IsHomogeneousElem` predicate because the output is independent
of a chosen degree.  The singleton homogeneity bridge is named so its remaining Prop proof debt is
visible rather than hidden in a data term; no redundant principal decomposition wrapper is exposed,
and callers that need it use the general `decomposition`.
In the noncommutative ambient generality, the principal ideal must separately be two-sided; this is
inferable for commutative rings and mathematically necessary otherwise.
-/

/-- A homogeneous element generates a homogeneous principal ideal. -/
@[stacks 00K1 "homogeneous principal ideal"]
theorem spanSingleton_isHomogeneous {a : A}
    (ha : SetLike.IsHomogeneousElem 𝒜 a) :
    (Ideal.span ({a} : Set A)).IsHomogeneous 𝒜 := sorry

/-- The canonical graded-algebra structure on the quotient by a homogeneous principal ideal. -/
@[reducible, stacks 00K1 "homogeneous principal quotient graded algebra"]
noncomputable def spanSingletonGradedAlgebra {a : A}
    [h_twoSided : (Ideal.span ({a} : Set A)).IsTwoSided]
    (ha : SetLike.IsHomogeneousElem 𝒜 a) :
    GradedAlgebra (grading 𝒜 (Ideal.span ({a} : Set A))) :=
  gradedAlgebra 𝒜 (Ideal.span ({a} : Set A))
    (spanSingleton_isHomogeneous 𝒜 ha)

end Graded

end GradedAlgebra.Quotient
