module

public import Mathlib.CategoryTheory.Sites.Sieves
public import Mathlib.CategoryTheory.Subobject.Limits
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap67.Definition_67_14_4_Subscheme
public import stacks_project.Chap67.Lemma_67_14_1_Quotient

/-!
# Completion along a closed subspace

The completion `completionAlongSubspace i` of an algebraic space `X` along a
closed immersion `i : Z ⟶ X` is the fppf sheaf of morphisms into `X` that
fppf-locally factor through some infinitesimal neighbourhood
`Z_n = V(I^{n+1})`. This is the colimit of the nested closed subspaces `Z_n`
in fppf sheaves, not the presheaf of morphisms that factor through a single
neighbourhood globally.

`Lemma_87_38_3_Completion` owns this sheaf but cannot be imported: it
redeclares `FormalAlgebraicSpace.IsFormalAlgebraicSpace`.
`Lemma_87_38_2_Completion` owns the global-factoring presheaf and is not
imported.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Opposite TypeCat
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

/-- The inclusion of a closed subspace is a closed immersion. -/
instance instIsClosedImmersion {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) : IsClosedImmersion Z.ι :=
  Z.isClosedImmersion

end ClosedSubspace

namespace Hom.InfinitesimalNeighbourhood

open Modules

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The multiplication map of the `(n + 1)`st tensor power of the kernel ideal of
a closed immersion into the structure module of the ambient space. -/
def powMul (n : ℕ) :
    ofComm
      (tensorObj
        (TensorPower.sheaf (commStructureSheaf X)
          (toCommSubobject (Hom.idealSheafSubobject i)) (n + 1))
        (toComm (SheafOfModules.unit (structureSheaf X)))) ⟶
      SheafOfModules.unit (structureSheaf X) :=
  ofCommMap
    (IdealSheaf.powerAction
      (toCommSubobject (Hom.idealSheafSubobject i))
      (toComm (SheafOfModules.unit (structureSheaf X))) (n + 1))

/-- `powMul i n` is the recast kernel-ideal power action into `𝒪_X`. -/
theorem powMul_eq (n : ℕ) :
    powMul i n =
      ofCommMap
        (IdealSheaf.powerAction
          (toCommSubobject (Hom.idealSheafSubobject i))
          (toComm (SheafOfModules.unit (structureSheaf X))) (n + 1)) :=
  sorry

/-- The quasi-coherent ideal sheaf on `X` defining the `n`th infinitesimal
neighbourhood. -/
def ideal (n : ℕ) : IdealSubobject X :=
  kernelSubobject (cokernel.π (powMul i n))

/-- The defining ideal of the `n`th infinitesimal neighbourhood is the image of
the kernel-ideal power multiplication map. -/
theorem ideal_eq_kernelSubobject (n : ℕ) :
    ideal i n = kernelSubobject (cokernel.π (powMul i n)) :=
  sorry

/-- The defining ideal of the `n`th infinitesimal neighbourhood is
quasi-coherent. -/
instance instIsQuasiCoherent_ideal (n : ℕ) : IsQuasiCoherent (ideal i n) :=
  sorry

/-- The `n`th infinitesimal neighbourhood of the source of a closed immersion, as
the closed subspace of `X` cut out by the `(n + 1)`st power of the kernel
ideal. -/
def space (n : ℕ) : AlgebraicSpace S :=
  subscheme (ideal i n)

/-- The infinitesimal-neighbourhood space is the closed subspace cut out by the
corresponding power of the kernel ideal. -/
theorem space_eq_subscheme (n : ℕ) :
    space i n = subscheme (ideal i n) :=
  sorry

/-- The canonical morphism from an infinitesimal neighbourhood to the ambient
algebraic space. -/
def toAmbient (n : ℕ) : space i n ⟶ X :=
  subschemeι (ideal i n)

/-- The ambient morphism of an infinitesimal neighbourhood is the closed-subspace
inclusion of its defining ideal. -/
theorem toAmbient_eq_subschemeι (n : ℕ) :
    toAmbient i n = subschemeι (ideal i n) :=
  sorry

end Hom.InfinitesimalNeighbourhood

/-- A Yoneda section of `X` factors through the `n`th infinitesimal neighbourhood
of a closed immersion `i : Z ⟶ X` when it lifts along
`Hom.InfinitesimalNeighbourhood.toAmbient i n`. -/
def factorsThroughNeighbourhood {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) {U : (Over S)ᵒᵖ}
    (x : X.functorOfPoints.obj U) : Prop :=
  ∃ y : (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints.obj U,
    (Hom.InfinitesimalNeighbourhood.toAmbient i n).app U y = x

/-- Factoring through the `n`th infinitesimal neighbourhood means lifting along
`Hom.InfinitesimalNeighbourhood.toAmbient i n`. -/
theorem factorsThroughNeighbourhood_iff {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) {U : (Over S)ᵒᵖ}
    (x : X.functorOfPoints.obj U) :
    factorsThroughNeighbourhood i n x ↔
      ∃ y : (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints.obj U,
        (Hom.InfinitesimalNeighbourhood.toAmbient i n).app U y = x :=
  sorry

/-- The image of a section of the `n`th infinitesimal neighbourhood under
`Hom.InfinitesimalNeighbourhood.toAmbient i n` factors through that
neighbourhood. -/
theorem factorsThroughNeighbourhood_toAmbient {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ)
    {U : (Over S)ᵒᵖ}
    (y : (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints.obj U) :
    factorsThroughNeighbourhood i n
      ((Hom.InfinitesimalNeighbourhood.toAmbient i n).app U y) :=
  sorry

/-- Factoring through an infinitesimal neighbourhood is stable under
precomposition with a morphism of schemes over `S`. -/
theorem factorsThroughNeighbourhood_map {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) {U V : (Over S)ᵒᵖ} (φ : U ⟶ V)
    {x : X.functorOfPoints.obj U} (hx : factorsThroughNeighbourhood i n x) :
    factorsThroughNeighbourhood i n (X.functorOfPoints.map φ x) :=
  sorry

/-- A Yoneda section of `X` fppf-locally factors through some infinitesimal
neighbourhood of `i` when it does so after restriction along an fppf cover. -/
def fppfLocallyFactorsThroughNeighbourhood {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] {U : (Over S)ᵒᵖ}
    (x : X.functorOfPoints.obj U) : Prop :=
  ∃ (ι : Type u) (cover : ι → Over S) (π : (j : ι) → cover j ⟶ U.unop),
    Sieve.ofArrows cover π ∈ Scheme.fppfTopology.over S U.unop ∧
      ∀ j, ∃ n, factorsThroughNeighbourhood i n
        (X.functorOfPoints.map (π j).op x)

/-- Unfolding of `fppfLocallyFactorsThroughNeighbourhood`. -/
theorem fppfLocallyFactorsThroughNeighbourhood_iff {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] {U : (Over S)ᵒᵖ}
    (x : X.functorOfPoints.obj U) :
    fppfLocallyFactorsThroughNeighbourhood i x ↔
      ∃ (ι : Type u) (cover : ι → Over S) (π : (j : ι) → cover j ⟶ U.unop),
        Sieve.ofArrows cover π ∈ Scheme.fppfTopology.over S U.unop ∧
          ∀ j, ∃ n, factorsThroughNeighbourhood i n
            (X.functorOfPoints.map (π j).op x) :=
  sorry

/-- A section that factors through some infinitesimal neighbourhood fppf-locally
factors through a neighbourhood. -/
theorem fppfLocallyFactorsThroughNeighbourhood.of_stage {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] {U : (Over S)ᵒᵖ}
    {x : X.functorOfPoints.obj U} (hx : ∃ n, factorsThroughNeighbourhood i n x) :
    fppfLocallyFactorsThroughNeighbourhood i x :=
  sorry

/-- Fppf-local factoring through an infinitesimal neighbourhood is stable under
precomposition with a morphism of schemes over `S`. -/
theorem fppfLocallyFactorsThroughNeighbourhood_map {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) {x : X.functorOfPoints.obj U}
    (hx : fppfLocallyFactorsThroughNeighbourhood i x) :
    fppfLocallyFactorsThroughNeighbourhood i (X.functorOfPoints.map φ x) :=
  sorry

/-- The completion of an algebraic space `X` along a closed subspace given by a
closed immersion `i : Z ⟶ X`, as the fppf sheaf of morphisms into `X` that
fppf-locally factor through some infinitesimal neighbourhood of `i`. -/
def completionAlongSubspace {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] : (Over S)ᵒᵖ ⥤ Type u where
  obj U :=
    { x : X.functorOfPoints.obj U // fppfLocallyFactorsThroughNeighbourhood i x }
  map φ :=
    ofHom fun x ↦
      ⟨X.functorOfPoints.map φ x.1,
        fppfLocallyFactorsThroughNeighbourhood_map i φ x.2⟩
  map_id := sorry
  map_comp := sorry

namespace completionAlongSubspace

/-- The canonical morphism `completionAlongSubspace i ⟶ X.functorOfPoints` from
the completion along the closed subspace. -/
def ι {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    completionAlongSubspace i ⟶ X.functorOfPoints where
  app _ := ofHom fun x ↦ x.1
  naturality := sorry

/-- Components of `ι i` are the subtype projections of
`completionAlongSubspace i`. -/
theorem ι_app {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : (Over S)ᵒᵖ) :
    (ι i).app U = ofHom fun x ↦ x.1 :=
  sorry

/-- A Yoneda section of `X` fppf-locally factors through some infinitesimal
neighbourhood of `i` if and only if it lifts through `ι i`. -/
theorem exists_lift {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] {U : (Over S)ᵒᵖ} (x : X.functorOfPoints.obj U) :
    fppfLocallyFactorsThroughNeighbourhood i x ↔ ∃ y, (ι i).app U y = x :=
  sorry

/-- The canonical morphism from the `n`th infinitesimal neighbourhood of a closed
immersion into the formal completion along that closed subspace. -/
def fromStage {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (n : ℕ) :
    (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints ⟶
      completionAlongSubspace i where
  app U :=
    ofHom fun y ↦
      ⟨(Hom.InfinitesimalNeighbourhood.toAmbient i n).app U y,
        fppfLocallyFactorsThroughNeighbourhood.of_stage i
          ⟨n, factorsThroughNeighbourhood_toAmbient i n y⟩⟩
  naturality := sorry

/-- Postcomposing `fromStage i n` with `ι i` recovers the neighbourhood inclusion
into `X`. -/
theorem fromStage_comp {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (n : ℕ) :
    fromStage i n ≫ ι i = Hom.InfinitesimalNeighbourhood.toAmbient i n :=
  sorry

/-- The canonical morphism from the completion along a closed subspace into the
ambient functor of points. -/
abbrev toFunctorOfPoints {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    completionAlongSubspace i ⟶ X.functorOfPoints :=
  ι i

/-- `toFunctorOfPoints i` is the subtype projection `ι i`. -/
theorem toFunctorOfPoints_eq {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    toFunctorOfPoints i = ι i :=
  sorry

end completionAlongSubspace

/-- The canonical morphism from the `n`th infinitesimal neighbourhood into the
formal completion along the closed subspace. -/
abbrev stageι {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (n : ℕ) :
    (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints ⟶
      completionAlongSubspace i :=
  completionAlongSubspace.fromStage i n

/-- On test objects, `stageι i n` is the image of
`Hom.InfinitesimalNeighbourhood.toAmbient i n` in the completion. -/
theorem stageι_app {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (n : ℕ) (U : (Over S)ᵒᵖ)
    (y : (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints.obj U) :
    (completionAlongSubspace.ι i).app U ((stageι i n).app U y) =
      (Hom.InfinitesimalNeighbourhood.toAmbient i n).app U y :=
  sorry

/-- The stage maps compose with `completionAlongSubspace.ι` to the ambient
neighbourhood inclusions. -/
theorem stageι_comp {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] (n : ℕ) :
    stageι i n ≫ completionAlongSubspace.ι i =
      Hom.InfinitesimalNeighbourhood.toAmbient i n :=
  sorry

/-- The completion along a closed subspace is the fppf sheaf of morphisms that
fppf-locally factor through some infinitesimal neighbourhood. -/
theorem completionAlongSubspace_eq {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (U : (Over S)ᵒᵖ) :
    (completionAlongSubspace i).obj U =
      { x : X.functorOfPoints.obj U //
        fppfLocallyFactorsThroughNeighbourhood i x } :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
