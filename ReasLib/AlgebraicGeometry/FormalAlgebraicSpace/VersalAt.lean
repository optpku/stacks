module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.CompletionAlong.Scheme
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Completion
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.KernelPair.Points

/-! # Formal objects and versality along scheme completions -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace GroupoidsOver
open FiberedCategoryOver Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The canonical morphism from a positive maximal-adic truncation of a
completed stalk to the original scheme, over the base. -/
def completionStageOverHom {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    (V : Over S) [AlgebraicGeometry.LocallyOfFiniteType V.hom]
    (v : V.left) [IsFiniteTypePoint v] (n : ℕ) :
    (completionSAlgebra V.hom v).stageOver n ⟶ V :=
  (completionSAlgebra V.hom v).truncationOverHom n ≫ fromSpecCompletionOverHom V.hom v

/-- Every positive maximal-adic stage at a point of a closed subset maps into
that subset. -/
theorem mapsInto_completionStage {S : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian S] {V : Over S}
    [AlgebraicGeometry.LocallyOfFiniteType V.hom] (Z : Closeds V.left)
    (v : V.left) [IsFiniteTypePoint v]
    (h_mem : ofOver.pointsEquiv V v ∈ pointsCloseds V Z) (n : ℕ) :
    mapsInto (pointsCloseds V Z : Set (Points (ofOver V)))
      (yonedaEquiv (ofOverMap (completionStageOverHom V v n))) :=
  sorry

/-- The section of the completion represented by a positive maximal-adic
truncation at a point of the closed subset. -/
def liftFromCompletionStage {S : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian S] {V : Over S}
    [AlgebraicGeometry.LocallyOfFiniteType V.hom] (Z : Closeds V.left)
    (v : V.left) [IsFiniteTypePoint v]
    (h_mem : ofOver.pointsEquiv V v ∈ pointsCloseds V Z) (n : ℕ) :
    (completionAlong (ofOver V) (pointsCloseds V Z)).obj
      (op ((completionSAlgebra V.hom v).stageOver n)) :=
  ⟨yonedaEquiv (ofOverMap (completionStageOverHom V v n)),
    mapsInto_completionStage Z v h_mem n⟩

/-- The underlying section of a lifted truncation is the Yoneda section of
its canonical morphism to the original scheme. -/
theorem liftFromCompletionStage_coe {S : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian S] {V : Over S}
    [AlgebraicGeometry.LocallyOfFiniteType V.hom] (Z : Closeds V.left)
    (v : V.left) [IsFiniteTypePoint v]
    (h_mem : ofOver.pointsEquiv V v ∈ pointsCloseds V Z) (n : ℕ) :
    (liftFromCompletionStage Z v h_mem n).1 =
      yonedaEquiv (ofOverMap (completionStageOverHom V v n)) := rfl

/-- Lifted truncation sections are compatible with the canonical successor
morphisms of the maximal-adic system. -/
theorem liftFromCompletionStage_naturality {S : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian S] {V : Over S}
    [AlgebraicGeometry.LocallyOfFiniteType V.hom] (Z : Closeds V.left)
    (v : V.left) [IsFiniteTypePoint v]
    (h_mem : ofOver.pointsEquiv V v ∈ pointsCloseds V Z) (n : ℕ) :
    (completionAlong (ofOver V) (pointsCloseds V Z)).map
        ((completionSAlgebra V.hom v).stageHom n).op
        (liftFromCompletionStage Z v h_mem (n + 1)) =
      liftFromCompletionStage Z v h_mem n :=
  sorry

-- Definitional reduction of the explicit completed-stalk stages needs a larger elaboration limit.
set_option maxHeartbeats 800000 in
/-- Applying a morphism from a scheme completion to the positive maximal-adic
stages at a point gives a formal object over its completed stalk. -/
def formalObjectAlong {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {V : Over S} [AlgebraicGeometry.LocallyOfFiniteType V.hom] {Z : Closeds V.left}
    {W : (Over S)ᵒᵖ ⥤ Type u}
    (g : completionAlong (ofOver V) (pointsCloseds V Z) ⟶ W) (v : V.left)
    [IsFiniteTypePoint v] (h_mem : ofOver.pointsEquiv V v ∈ pointsCloseds V Z) :
    FormalObject (FiberedCategoryOver.Groupoids.ofPresheaf W) := by
  let R := completionSAlgebra V.hom v
  let sectionAt := fun n ↦ g.app (op (R.stageOver n)) (liftFromCompletionStage Z v h_mem n)
  let objects := fun n ↦ (Sets.ofPresheaf.valueToFiber W (R.stageOver n) (sectionAt n)).1
  let step : ∀ n, objects n ⟶ objects (n + 1) := fun n ↦
    (CategoryOfElements.homMk
      (⟨op (R.stageOver (n + 1)), sectionAt (n + 1)⟩ : W.Elements)
      (⟨op (R.stageOver n), sectionAt n⟩ : W.Elements)
      (R.stageHom n).op (by
        change W.map (R.stageHom n).op
            (g.app (op (R.stageOver (n + 1))) (liftFromCompletionStage Z v h_mem (n + 1))) =
          g.app (op (R.stageOver n)) (liftFromCompletionStage Z v h_mem n)
        have h :
            g.app (op (R.stageOver n))
                ((completionAlong (ofOver V) (pointsCloseds V Z)).map (R.stageHom n).op
                  (liftFromCompletionStage Z v h_mem (n + 1))) =
              W.map (R.stageHom n).op
                (g.app (op (R.stageOver (n + 1)))
                  (liftFromCompletionStage Z v h_mem (n + 1))) :=
          ConcreteCategory.congr_hom (g.naturality (R.stageHom n).op)
            (liftFromCompletionStage Z v h_mem (n + 1))
        exact h.symm.trans
          (congrArg (fun x ↦ g.app (op (R.stageOver n)) x)
            (liftFromCompletionStage_naturality Z v h_mem n)))).op
  exact GroupoidsOver.FormalObject.of R objects step (fun _ ↦ rfl)
    (fun n ↦ Functor.IsHomLift.map (step n))

/-- The complete local `S`-algebra of `formalObjectAlong` is the completed stalk
`𝒪_{V,v}^∧`. -/
theorem formalObjectAlong_base {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {V : Over S} [AlgebraicGeometry.LocallyOfFiniteType V.hom] {Z : Closeds V.left}
    {W : (Over S)ᵒᵖ ⥤ Type u}
    (g : completionAlong (ofOver V) (pointsCloseds V Z) ⟶ W) (v : V.left)
    [IsFiniteTypePoint v] (h_mem : ofOver.pointsEquiv V v ∈ pointsCloseds V Z) :
    (formalObjectAlong g v h_mem).base = completionSAlgebra V.hom v := rfl

/-- Stage `n` of `formalObjectAlong` lies over
`(completionSAlgebra V.hom v).stageOver n`. -/
theorem formalObjectAlong_spec {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {V : Over S} [AlgebraicGeometry.LocallyOfFiniteType V.hom] {Z : Closeds V.left}
    {W : (Over S)ᵒᵖ ⥤ Type u}
    (g : completionAlong (ofOver V) (pointsCloseds V Z) ⟶ W) (v : V.left)
    [IsFiniteTypePoint v] (h_mem : ofOver.pointsEquiv V v ∈ pointsCloseds V Z)
    (n : ℕ) :
    (FiberedCategoryOver.Groupoids.ofPresheaf W).p.obj ((formalObjectAlong g v h_mem).objects n) =
      (completionSAlgebra V.hom v).stageOver n := rfl

/-- A morphism from a scheme completion is versal at a finite type point
when that point lies in the closed subset and its associated completed-stalk
formal object is versal on objects. -/
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

end AlgebraicGeometry.FormalAlgebraicSpace
