module

public import ReasLib.CategoryTheory.Sites.Simplicial.SliceAugmentation
import StacksCheckRecall

/-!
# Lemma 85.21.5

The slice sites of a simplicial object with fibre products form a simplicial
site. Its total site has the pullback-hom presentation and identity-degree
coverings, and an augmentation induces the canonical total morphism of topoi.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject
open scoped Simplicial

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : GrothendieckTopology C) (U : SimplicialObject C)
variable {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)

/- Lemma 85.21.5 (1): the slice sites form a simplicial site. The localization
morphisms are presented continuously by their pullback right adjoints. -/
@[stacks 09WL] #check
  (CategoryTheory.SimplicialObject.sliceStructurePullback_isContinuous J U φ :
    Functor.Precoverage.IsContinuous (Over.pullback (U.map φ))
      (slicePrecoverage J U m) (slicePrecoverage J U n))

#check (CategoryTheory.Functor.ContinuousRightAdjoint.right_isMorphismOfSites
    (Over.map (U.map φ)) (Over.pullback (U.map φ)) (Over.mapPullbackAdj (U.map φ)) :
  IsMorphismOfSites (J.over (U.obj m)) (J.over (U.obj n)) (Over.pullback (U.map φ)))

#check (CategoryTheory.GrothendieckTopology.overMapPushforwardIsoCocontinuous
    J (Type (max u v)) (U.map φ) :
  J.overMapPushforward (Type (max u v)) (U.map φ) ≅
    (Over.map (U.map φ)).sheafPushforwardCocontinuous (Type (max u v))
      (J.over (U.obj n)) (J.over (U.obj m)))

#check (CategoryTheory.SimplicialObject.sliceStructurePullback_compIso U :
  ∀ {i j k : SimplexCategoryᵒᵖ} (α : i ⟶ j) (β : j ⟶ k),
    Over.pullback (U.map (α ≫ β)) ≅
      Over.pullback (U.map β) ⋙ Over.pullback (U.map α))

variable {T S : sliceTotalSite U} {I : Type (max u v)}
variable (V : I → Over (U.obj T.base)) (p : ∀ i, V i ⟶ T.fiber)

/- Lemma 85.21.5 (2): the total-site construction reproduces the slice total
site through the adjunction description of arrows and the same stage covers. -/
@[stacks 09WL] #check
  (CategoryTheory.SimplicialObject.sliceTotal_reproduces J U V p :
    Function.Bijective
        (sliceTotalHom_pullbackEquiv U :
          (T ⟶ S) → Σ α : S.base.unop ⟶ T.base.unop,
            T.fiber ⟶ (Over.pullback (U.map α.op)).obj S.fiber) ∧
      (Grothendieck.ofFiber (sliceDiagram U) T V p ∈ sliceTotalPrecoverage J U T ↔
        Presieve.ofArrows V p ∈ slicePrecoverage J U T.base T.fiber))

#check (CategoryTheory.SimplicialObject.sliceTotalHom_pullbackEquiv_comp U :
  ∀ {T S R : sliceTotalSite U} (f : T ⟶ S) (g : S ⟶ R),
    (Over.mapPullbackAdj (U.map (f.base ≫ g.base))).homEquiv T.fiber R.fiber (f ≫ g).fiber =
      (sliceTotalHom_pullbackEquiv U f).2 ≫
        (Over.pullback (U.map f.base)).map (sliceTotalHom_pullbackEquiv U g).2 ≫
        (sliceStructurePullback_compIso U f.base g.base).inv.app R.fiber)

variable {X : C} (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

#check (CategoryTheory.SimplicialObject.sliceDiagram_isAugmentation J U a :
  Grothendieck.IsAugmentation (sliceDiagram U) (slicePrecoverage J U)
    (J.over X).toPrecoverage (Over.map (a.app (op ⦋0⦌))))

#check (CategoryTheory.GrothendieckTopology.overPullback_isContinuous J (a.app (op ⦋0⦌)) :
  (Over.pullback (a.app (op ⦋0⦌))).IsContinuous
    (J.over X) (J.over (U.obj (op ⦋0⦌))))

#check (CategoryTheory.SimplicialObject.slicePullback_compIso U a :
  ∀ {n : SimplexCategory} (α β : ⦋0⦌ ⟶ n),
    Over.pullback (a.app (op ⦋0⦌)) ⋙ Over.pullback (U.map α.op) ≅
      Over.pullback (a.app (op ⦋0⦌)) ⋙ Over.pullback (U.map β.op))

/- Lemma 85.21.5 (3): the degree-zero localization is an augmentation and the
morphism of topoi induced by the generic total augmentation agrees with the
one presented by sending V/U_n to V/X. -/
@[stacks 09WL] #check
  (CategoryTheory.SimplicialObject.sliceAugmentation_pushforwardIso J U a :
    ((sliceAugmentationTopos J U a).pushforward :
      Sheaf (sliceTotalTopology J U) (Type (max u v)) ⥤
        Sheaf (J.over X) (Type (max u v))) ≅
      (sliceAugmentationTopos_ofAugmentation J U a).pushforward)

#check (CategoryTheory.SimplicialObject.sliceAugmentation_inverseImageIso J U a :
  ((sliceAugmentationTopos J U a).inverseImage :
    Sheaf (J.over X) (Type (max u v)) ⥤
      Sheaf (sliceTotalTopology J U) (Type (max u v))) ≅
    (sliceAugmentationTopos_ofAugmentation J U a).inverseImage)
