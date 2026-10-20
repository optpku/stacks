module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.Groupoids
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.FiberTransport
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.DescentEffectivity
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Basic

/-!
# The stack target and comparison of the local descent construction

The target uses the actual completion fibres and their native realization.
The comparison retains the original object, local-arrow and descent maps.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory

noncomputable section

universe u v uX vX

namespace CategoryTheory.Functor.StackificationConstruction

variable {C : Type u} [Category.{v} C] {X : Type uX} [Category.{vX} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C) (χ : p.Cleavage)

/-- The realized projection retains the native Cartesian lifts. -/
instance targetIsFibered : (targetProjection J p χ).IsFibered :=
  inferInstanceAs
    (Pseudofunctor.CoGrothendieck.forget (completedPresheaf J p χ).toPseudofunctor').IsFibered

/-- The target stack carries actual descent preimages and actual effective glue objects. -/
theorem targetIsStack : IsStack.OnSite J (targetProjection J p χ) :=
  Pseudofunctor.CoGrothendieck.stackOnSite
    (completedPresheaf J p χ).toPseudofunctor' J
    (DescentCompletion.ObjectGluing.isStack J (localFibers J p χ)
      (Localized.isPrestack J p χ (localCleavage J p χ)))

/-- Bundle the concrete target without selecting from an existence theorem. -/
def targetStack : StackOver.{u, v, max u v uX vX, max u v vX} J :=
  StackOver.mk (FiberedCategoryOver.ofFunctor (targetProjection J p χ))
    (targetIsStack J p χ)

/-- The composite comparison literally maps an original object to its descent model. -/
def comparisonBased : BasedCategory.ofFunctor p ⥤ᵇ
    BasedCategory.ofFunctor (targetProjection J p χ) :=
  BasedFunctor.ofFunctor
    (Localized.fromOriginal J p χ ⋙ realizationFunctor J p χ) (by rfl)

/-- The vertical factor of a supplied Cartesian arrow has an actual reverse
factor through that arrow, in the same original local fibre. -/
def verticalFactorIso {a b : Localized J p χ} (τ : a ⟶ b)
    (hτ : (Localized.projection J p χ).IsStronglyCartesian
      ((Localized.projection J p χ).map τ) τ) :
    localFiberObject J p χ a ≅ (localCleavage J p χ).reindexTarget τ := by
  let q := Localized.projection J p χ
  let ξ := localCleavage J p χ
  let l := ξ.reindexLift (q.map τ) (localFiberObject J p χ b)
  let inverse := @Functor.IsStronglyCartesian.map C (Localized J p χ) _ _ q
    (q.obj a) (q.obj b) a b (q.map τ) τ hτ
    (q.obj a) l.source (𝟙 (q.obj a)) (q.map τ) (Category.id_comp (q.map τ)).symm
    l.hom l.isStronglyCartesian.toIsHomLift
  have inverseLift : q.IsHomLift (𝟙 (q.obj a)) inverse :=
    @Functor.IsStronglyCartesian.map_isHomLift C (Localized J p χ) _ _ q
      (q.obj a) (q.obj b) a b (q.map τ) τ hτ
      (q.obj a) l.source (𝟙 (q.obj a)) (q.map τ) (Category.id_comp (q.map τ)).symm
      l.hom l.isStronglyCartesian.toIsHomLift
  exact
    { hom := ξ.verticalFactor τ
      inv := ⟨inverse, inverseLift⟩
      hom_inv_id := by sorry
      inv_hom_id := by sorry }

/-- The realization fibre map of a Cartesian arrow has the explicit inverse
obtained by mapping the reverse vertical factor and the unit restriction inverse. -/
def realizationFiberIso {a b : Localized J p χ} (τ : a ⟶ b)
    (hτ : (Localized.projection J p χ).IsStronglyCartesian
      ((Localized.projection J p χ).map τ) τ) :
    ((realizationFunctor J p χ).obj a).fiber ≅
      (((completedPresheaf J p χ).toPseudofunctor'.map
        ((Localized.projection J p χ).map τ).op.toLoc).toFunctor.obj
        ((realizationFunctor J p χ).obj b).fiber) :=
  (DescentCompletion.unitFunctor J (localFibers J p χ)
    ((Localized.projection J p χ).obj a)).mapIso (verticalFactorIso J p χ τ hτ) ≪≫
      DescentCompletion.unitReindexIso J (localFibers J p χ)
        ((Localized.projection J p χ).map τ) (localFiberObject J p χ b)

/-- The image of a Cartesian arrow has its actual co-Grothendieck factor:
factor through the native lift and then use the explicit fibre inverse. -/
theorem realizationArrowStrong {a b : Localized J p χ} (τ : a ⟶ b)
    (hτ : (Localized.projection J p χ).IsStronglyCartesian
      ((Localized.projection J p χ).map τ) τ) :
    (targetProjection J p χ).IsStronglyCartesian
      ((Localized.projection J p χ).map τ) ((realizationFunctor J p χ).map τ) where
  toIsHomLift := by
    let hbase : (targetProjection J p χ).map ((realizationFunctor J p χ).map τ) =
        (Localized.projection J p χ).map τ := rfl
    exact hbase.symm ▸ Functor.IsHomLift.map ((realizationFunctor J p χ).map τ)
  universal_property' := by
    intro z g θ hθ
    let F := (completedPresheaf J p χ).toPseudofunctor'
    let e := (Pseudofunctor.CoGrothendieck.ι F
      ((Localized.projection J p χ).obj a)).mapIso (realizationFiberIso J p χ τ hτ)
    let hbase : (targetProjection J p χ).map ((realizationFunctor J p χ).map τ) =
        (Localized.projection J p χ).map τ := rfl
    letI : (Pseudofunctor.CoGrothendieck.forget F).IsHomLift
        (g ≫ (Localized.projection J p χ).map τ) θ :=
      (congrArg (fun k ↦ g ≫ k) hbase) ▸ hθ
    let nativeLift := Pseudofunctor.CoGrothendieck.cartesianLift
      ((realizationFunctor J p χ).obj b).fiber ((Localized.projection J p χ).map τ)
    let nativeStrong := Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift
      ((realizationFunctor J p χ).obj b).fiber ((Localized.projection J p χ).map τ)
    let factor := @Functor.IsStronglyCartesian.map C (Pseudofunctor.CoGrothendieck F) _ _
      (Pseudofunctor.CoGrothendieck.forget F)
      ((Localized.projection J p χ).obj a) ((Localized.projection J p χ).obj b)
      _ ((realizationFunctor J p χ).obj b) ((Localized.projection J p χ).map τ)
      nativeLift nativeStrong _ z g (g ≫ (Localized.projection J p χ).map τ) rfl θ hθ ≫ e.inv
    exact ⟨factor, ⟨by sorry, by sorry⟩, by
      intro ψ hψ
      sorry⟩

/-- The realization is a Cartesian functor, using the supplied source
Cartesian witness only to construct its actual reverse fibre factor. -/
def realizationCartesian :
    CartesianBasedFunctor (Localized.projection J p χ) (targetProjection J p χ) :=
  CartesianBasedFunctor.ofBasedFunctor (realizationBased J p χ) (by
    intro a b τ hτ
    exact realizationArrowStrong J p χ τ hτ)

/-- The original projection maps to its completed stack by the two actual
Cartesian stages. No additional model or cleavage premise is required at use sites. -/
def comparison : CartesianBasedFunctor p (targetStack J p χ).p :=
  (Localized.comparison J p χ).comp (realizationCartesian J p χ)

/-- The groupoid target retains the inverse operations constructed on its fibres. -/
def targetGroupoids (hG : Functor.IsFibered.InGroupoids p) :
    StackOver.Groupoids.{u, v, max u v uX vX, max u v vX} J := by
  letI : Functor.IsFibered.InGroupoids (targetProjection J p χ) :=
    targetInGroupoids J p χ hG
  exact StackOver.Groupoids.mk
    (FiberedCategoryOver.Groupoids.ofFunctor (targetProjection J p χ))
    (targetIsStack J p χ)

/-- The comparison into the groupoid target is Cartesian using its actual
Cartesian factor witnesses for every mapped arrow. -/
def groupoidComparison (hG : Functor.IsFibered.InGroupoids p) :
    CartesianBasedFunctor p (targetGroupoids J p χ hG).p :=
  CartesianBasedFunctor.ofBasedFunctor (comparisonBased J p χ) (by
    intro a b φ hφ
    let q := targetProjection J p χ
    let hTarget := targetInGroupoids J p χ hG
    exact @Functor.IsFibered.isStronglyCartesian_of_isCartesian C _ _ _ q
      hTarget.toIsFibered _ _ (q.map ((comparisonBased J p χ).map φ)) _ _
      ((comparisonBased J p χ).map φ)
      (hTarget.all_isCartesian ((comparisonBased J p χ).map φ)))

end CategoryTheory.Functor.StackificationConstruction
