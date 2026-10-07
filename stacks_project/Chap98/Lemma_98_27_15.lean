module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap87.Lemma_87_14_4_Completion
public import stacks_project.Chap87.Lemma_87_20_11_InfinitesimalStages
public import stacks_project.Chap98.Lemma_98_12_7_Approximate
import Mathlib.Tactic.CrossRefAttribute

/-!
# Openness of smoothness for an adic versal morphism of formal algebraic spaces

If `g : V_/Z ⟶ W` is an adic morphism of formal algebraic spaces which is
versal at a closed point of `V`, then after replacing `V` by an open
neighbourhood of that point the morphism is smooth in the Bootstrap sense:
representable by algebraic spaces, with smooth Yoneda pullbacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace GroupoidsOver
open FiberedCategoryOver Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Transport a closed subset `Z ⊂ V` along `ofOver.pointsHomeomorph` to a closed
subset of `Points (ofOver V)`. -/
def pointsCloseds {S : Scheme.{u}} (V : Over S) (Z : Closeds V.left) :
    Closeds (Points (ofOver V)) where
  carrier := Set.image (ofOver.pointsHomeomorph V) (Z : Set V.left)
  isClosed' := (ofOver.pointsHomeomorph V).isClosedMap (Z : Set V.left) Z.isClosed

/-- A point of `ofOver V` lies in `pointsCloseds V Z` if and only if it is the
image of a point of `Z`. -/
theorem mem_pointsCloseds {S : Scheme.{u}} {V : Over S} {Z : Closeds V.left}
    {x : Points (ofOver V)} :
    x ∈ pointsCloseds V Z ↔ ∃ z ∈ Z, ofOver.pointsEquiv V z = x :=
  sorry

/-- The open immersion `V' ⟶ V` as a morphism of schemes over `S`. -/
def openOverHom {S : Scheme.{u}} {V : Over S} (V' : V.left.Opens) :
    Over.mk (Scheme.Opens.ι V' ≫ V.hom) ⟶ V :=
  Over.homMk (Scheme.Opens.ι V') sorry

/-- The underlying scheme morphism of `openOverHom` is the open immersion of
`V'`. -/
theorem openOverHom_left {S : Scheme.{u}} {V : Over S} (V' : V.left.Opens) :
    (openOverHom V').left = Scheme.Opens.ι V' :=
  sorry

/-- The morphism of completions induced by an open immersion `V' ⟶ V`, from the
completion of `V'` along the preimage of `Z` to the completion of `V` along
`Z`. -/
def restrictAlong {S : Scheme.{u}} {V : Over S} (Z : Closeds V.left)
    (V' : V.left.Opens) :=
  completionAlong.map (ofOverMap (openOverHom V')) (pointsCloseds V Z)

/-- Restricting the completion along an open neighbourhood of `V` and then
including into `V` recovers the functor-of-points map of the open immersion. -/
theorem restrictAlong_comp_ι {S : Scheme.{u}} {V : Over S} (Z : Closeds V.left)
    (V' : V.left.Opens) :
    restrictAlong Z V' ≫ completionAlong.ι (ofOver V) (pointsCloseds V Z) =
      completionAlong.ι (ofOver (Over.mk (Scheme.Opens.ι V' ≫ V.hom)))
          ((pointsCloseds V Z).preimage
            (Points.continuous_map (ofOverMap (openOverHom V')))) ≫
        ofOverMap (openOverHom V') :=
  sorry

/-- The category fibred in groupoids associated to a functor of points on
schemes over `S`. -/
def groupoidsOfPresheaf {S : Scheme.{u}} (W : (Over S)ᵒᵖ ⥤ Type u) :
    GroupoidsOver S :=
  (Sets.toGroupoids (Over S)).obj ((Sets.ofPresheaf (Over S)).obj W)

/-- `groupoidsOfPresheaf W` is the discrete Grothendieck construction of `W`,
forgotten from sets to groupoids. -/
theorem groupoidsOfPresheaf_eq {S : Scheme.{u}} (W : (Over S)ᵒᵖ ⥤ Type u) :
    groupoidsOfPresheaf W =
      (Sets.toGroupoids (Over S)).obj ((Sets.ofPresheaf (Over S)).obj W) :=
  sorry

/-- The lift of `fromSpecCompletion v` through the completion of `V` along `Z`. -/
def liftFromSpecCompletion {S : Scheme.{u}} {V : Over S} (Z : Closeds V.left)
    (v : V.left) (h_mem : ofOver.pointsEquiv V v ∈ pointsCloseds V Z) :
    (completionAlong (ofOver V) (pointsCloseds V Z)).obj
      (op (Over.mk (fromSpecCompletion v ≫ V.hom))) :=
  ⟨yonedaEquiv (ofOverMap (Over.homMk (fromSpecCompletion v))), sorry⟩

/-- The underlying functor-of-points section of `liftFromSpecCompletion` is the
Yoneda class of `fromSpecCompletion v`. -/
theorem liftFromSpecCompletion_coe {S : Scheme.{u}} {V : Over S}
    (Z : Closeds V.left) (v : V.left)
    (h_mem : ofOver.pointsEquiv V v ∈ pointsCloseds V Z) :
    (liftFromSpecCompletion Z v h_mem).1 =
      yonedaEquiv (ofOverMap (Over.homMk (fromSpecCompletion v))) :=
  sorry

/-- The associated formal object of `W` at `v`, obtained by applying `g` to the
lift of `Spec(𝒪_{V,v}^∧) ⟶ V` through `V_/Z` and restricting along maximal-adic
truncations. -/
def formalObjectAlong {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S] {V : Over S}
    [AlgebraicGeometry.LocallyOfFiniteType V.hom] {Z : Closeds V.left}
    {W : (Over S)ᵒᵖ ⥤ Type u}
    (g : completionAlong (ofOver V) (pointsCloseds V Z) ⟶ W) (v : V.left)
    [IsFiniteTypePoint v] (h_mem : ofOver.pointsEquiv V v ∈ pointsCloseds V Z) :
    FormalObject (groupoidsOfPresheaf W) :=
  FormalObject.restriction <|
    CompleteLocalObject.of (completionSAlgebra V.hom v)
      (Sets.ofPresheaf.valueToFiber W (Over.mk (fromSpecCompletion v ≫ V.hom))
        (g.app (op (Over.mk (fromSpecCompletion v ≫ V.hom)))
          (liftFromSpecCompletion Z v h_mem))).1
      sorry

/-- The complete local `S`-algebra of `formalObjectAlong` is the completed stalk
`𝒪_{V,v}^∧`. -/
theorem formalObjectAlong_base {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {V : Over S} [AlgebraicGeometry.LocallyOfFiniteType V.hom] {Z : Closeds V.left}
    {W : (Over S)ᵒᵖ ⥤ Type u}
    (g : completionAlong (ofOver V) (pointsCloseds V Z) ⟶ W) (v : V.left)
    [IsFiniteTypePoint v] (h_mem : ofOver.pointsEquiv V v ∈ pointsCloseds V Z) :
    (formalObjectAlong g v h_mem).base = completionSAlgebra V.hom v :=
  sorry

/-- Stage `n` of `formalObjectAlong` lies over
`(completionSAlgebra V.hom v).stageOver n`. -/
theorem formalObjectAlong_spec {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {V : Over S} [AlgebraicGeometry.LocallyOfFiniteType V.hom] {Z : Closeds V.left}
    {W : (Over S)ᵒᵖ ⥤ Type u}
    (g : completionAlong (ofOver V) (pointsCloseds V Z) ⟶ W) (v : V.left)
    [IsFiniteTypePoint v] (h_mem : ofOver.pointsEquiv V v ∈ pointsCloseds V Z)
    (n : ℕ) :
    (groupoidsOfPresheaf W).p.obj ((formalObjectAlong g v h_mem).objects n) =
      (completionSAlgebra V.hom v).stageOver n :=
  sorry

/-- An adic morphism `g : V_/Z ⟶ W` is versal at `v` in the sense of Section
98.15 when `v` lies on `Z` and the associated formal object of `W` at `v` is
versal on objects. -/
class IsVersalAt {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S] {V : Over S}
    [AlgebraicGeometry.LocallyOfFiniteType V.hom] (Z : Closeds V.left)
    {W : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace W]
    (g : completionAlong (ofOver V) (pointsCloseds V Z) ⟶ W) (v : V.left)
    [IsFiniteTypePoint v] : Prop where
  /-- The point `v` lies on the closed subset `Z`. -/
  mem_closed : ofOver.pointsEquiv V v ∈ pointsCloseds V Z
  /-- The associated formal object of `W` at `v` is versal on objects. -/
  isVersal : FormalObject.IsVersalOnObjects (formalObjectAlong g v mem_closed)

/-- The identity of the completion of `V` along `V` itself is versal at a finite
type point. -/
instance instIsVersalAt_id {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {V : Over S} [AlgebraicGeometry.LocallyOfFiniteType V.hom]
    [IsFormalAlgebraicSpace (completionAlong (ofOver V) (pointsCloseds V ⊤))]
    (v : V.left) [IsFiniteTypePoint v] :
    IsVersalAt (⊤ : Closeds V.left)
      (𝟙 (completionAlong (ofOver V) (pointsCloseds V ⊤))) v :=
  sorry

/-- Versality of `g` at `v` unpacks as membership of `v` in `Z` together with
versality on objects of the associated formal object. -/
theorem isVersalAt_iff {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S] {V : Over S}
    [AlgebraicGeometry.LocallyOfFiniteType V.hom] (Z : Closeds V.left)
    {W : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace W]
    (g : completionAlong (ofOver V) (pointsCloseds V Z) ⟶ W) (v : V.left)
    [IsFiniteTypePoint v] :
    IsVersalAt Z g v ↔
      ∃ h_mem : ofOver.pointsEquiv V v ∈ pointsCloseds V Z,
        FormalObject.IsVersalOnObjects (formalObjectAlong g v h_mem) :=
  sorry

/-- The two defining conditions of `IsVersalAt`: `v` lies on `Z`, and the
associated formal object is versal on objects. -/
theorem IsVersalAt.spec {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S] {V : Over S}
    [AlgebraicGeometry.LocallyOfFiniteType V.hom] {Z : Closeds V.left}
    {W : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace W]
    {g : completionAlong (ofOver V) (pointsCloseds V Z) ⟶ W} {v : V.left}
    [IsFiniteTypePoint v] (h : IsVersalAt Z g v) :
    ofOver.pointsEquiv V v ∈ pointsCloseds V Z ∧
      FormalObject.IsVersalOnObjects (formalObjectAlong g v h.mem_closed) :=
  sorry

/-- Lemma 98.27.15. Let `S` be a locally Noetherian scheme. Let `V` be a scheme
locally of finite type over `S`. Let `Z ⊂ V` be closed. Let `W` be a locally
Noetherian formal algebraic space over `S` such that `W_red` is locally of
finite type over `S`. Let `g : completionAlong (ofOver V) (pointsCloseds V Z) ⟶ W`
be an adic morphism of formal algebraic spaces over `S`, in the sense that `g`
is representable by algebraic spaces. Let `v ∈ V` be a closed point such that
`g` is versal at `v` as in Section 98.15. Then after replacing `V` by an open
neighbourhood of `v` the morphism `g` is smooth in the Bootstrap sense:
representable by algebraic spaces, with smooth Yoneda pullbacks. -/
@[stacks 0GI9]
theorem exists_isSmooth_nhd {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {V : Over S} [AlgebraicGeometry.LocallyOfFiniteType V.hom] (Z : Closeds V.left)
    {W : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian W] [Reduction W]
    [AlgebraicSpace.LocallyOfFiniteType (toBase (reduction W))]
    (g : completionAlong (ofOver V) (pointsCloseds V Z) ⟶ W)
    (hg : representableByAlgebraicSpaces g) (v : V.left) (hv : IsClosed {v})
    [IsFiniteTypePoint v] [IsVersalAt Z g v] :
    ∃ V' : V.left.Opens,
      v ∈ V' ∧
        representableByAlgebraicSpaces (restrictAlong Z V' ≫ g) ∧
          ∀ (ha : representableByAlgebraicSpaces (restrictAlong Z V' ≫ g))
            ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ W),
            AlgebraicSpace.Smooth (ha.pullbackHom ξ) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
