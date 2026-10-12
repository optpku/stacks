/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_21_5_Augmentation
public import stacks_project.Chap85.Lemma_85_21_5_Comparison
public import stacks_project.Chap85.Lemma_85_21_5_Diagram

/-!
# Lemma 85.21.5

A simplicial object of a site with fibre products yields a simplicial object of
sites `C / U_n`, whose total site reproduces `(C / U)_total`, and an augmentation
`a : U ⟶ X` induces the same morphism of topoi as `V / U_n ↦ V / X`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite Functor
open scoped Simplicial
open CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable [HasPullbacks C]
variable (J : GrothendieckTopology C) (U : SimplicialObject C)

/-- Lemma 85.21.5 (1): `C / U` has the structure of a simplicial object in the category
whose objects are sites and whose morphisms are morphisms of sites. For each structure
map `φ`, `Over.pullback (U.map φ)` is continuous for the slice precoverages
(`sliceStructurePullback_isContinuous`); these continuous functors are the structure
maps, with composition the isomorphism `sliceStructurePullback_compIso` rather than a
strict `Cat` functor. `Over.map (U.map φ)` induces the same morphism of topoi by Sites
Lemma 7.27.3. -/
@[stacks 09WL]
noncomputable abbrev sliceStructureMap_sameTopos {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
    [∀ P : (Over (U.obj n))ᵒᵖ ⥤ Type w,
      (Over.map (U.map φ)).op.HasPointwiseRightKanExtension P] :
    J.overMapPushforward (Type w) (U.map φ) ≅
      (Over.map (U.map φ)).sheafPushforwardCocontinuous (Type w)
        (J.over (U.obj n)) (J.over (U.obj m)) :=
  J.overMapPushforwardIsoCocontinuous (Type w) (U.map φ)

/-- `sliceStructureMap_sameTopos` is the Sites Lemma 7.27.3 comparison on `U.map φ`. -/
theorem sliceStructureMap_sameTopos_eq {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
    [∀ P : (Over (U.obj n))ᵒᵖ ⥤ Type w,
      (Over.map (U.map φ)).op.HasPointwiseRightKanExtension P] :
    sliceStructureMap_sameTopos J U φ =
      J.overMapPushforwardIsoCocontinuous (Type w) (U.map φ) :=
  sorry

/-- Lemma 85.21.5 (2): the construction of Lemma 85.3.1 applied to the slice diagram of
(1) reproduces the site `(C / U)_total`: morphisms `V / U_n ⟶ W / U_m` are equivalent,
via `sliceTotalHom_pullbackEquiv`, to a simplex operator `φ` together with a morphism
`V ⟶ W ×_{U_m} U_n` over `U_n`, and covering families are the identity-degree stage
covers from `J.over U_n`. -/
@[stacks 09WL]
theorem sliceTotal_reproduces {X Y : sliceTotalSite U}
    {I : Type (max u v)} (V : I → Over (U.obj X.base)) (p : ∀ i, V i ⟶ X.fiber) :
    Function.Bijective
        (sliceTotalHom_pullbackEquiv U :
          (X ⟶ Y) →
            Σ φ : Y.base.unop ⟶ X.base.unop,
              X.fiber ⟶ (Over.pullback (U.map φ.op)).obj Y.fiber) ∧
      (Grothendieck.ofFiber (sliceDiagram U) X V p ∈ sliceTotalPrecoverage J U X ↔
        Presieve.ofArrows V p ∈ slicePrecoverage J U X.base X.fiber) :=
  sorry

variable {X : C} (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)
variable [HasSheafify (sliceTotalTopology J U) (Type w)]
variable [∀ P : (sliceTotalSite U)ᵒᵖ ⥤ Type w, (sliceForget U a).op.HasPointwiseRightKanExtension P]
variable [∀ P : (sliceTotalSite U)ᵒᵖ ⥤ Type w,
    (sliceForget_ofAugmentation U a).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (sliceTotalTopology J U) (Type w)]

/-- Lemma 85.21.5 (3): if `a : U ⟶ X` is an augmentation, then `a0 : C / U_0 ⟶ C / X`
is an augmentation as in Remark 85.4.1 (A): `Over.pullback (a.app (op ⦋0⦌))` is
continuous (`slicePullback_precoverage_isContinuous`), and for `φ, ψ : ⦋0⦌ ⟶ n` the
composites `u_φ ∘ u0` agree by the canonical pullback isomorphism. The total morphism
of topoi presented by `sliceForget` is isomorphic to the morphism induced by that
part (A) augmentation. -/
@[stacks 09WL]
noncomputable def sliceAugmentation_spec {n : SimplexCategory} (φ ψ : ⦋0⦌ ⟶ n) :
    (Over.pullback (a.app (op ⦋0⦌)) ⋙ Over.pullback (U.map φ.op) ≅
      Over.pullback (a.app (op ⦋0⦌)) ⋙ Over.pullback (U.map ψ.op)) ×
    ((sliceAugmentationTopos J U a).pushforward ≅
      (sliceAugmentationTopos_ofAugmentation J U a).pushforward) :=
  (slicePullback_compIso U a φ ψ, sliceAugmentation_pushforwardIso J U a)

/-- The first factor of `sliceAugmentation_spec` is `slicePullback_compIso`. -/
theorem sliceAugmentation_spec_compIso {n : SimplexCategory} (φ ψ : ⦋0⦌ ⟶ n) :
    (sliceAugmentation_spec J U a φ ψ).1 = slicePullback_compIso U a φ ψ :=
  sorry

/-- The second factor of `sliceAugmentation_spec` is the direct-image comparison of
`sliceAugmentationTopos` with the part (A) total morphism. -/
theorem sliceAugmentation_spec_pushforward {n : SimplexCategory} (φ ψ : ⦋0⦌ ⟶ n) :
    (sliceAugmentation_spec J U a φ ψ).2 = sliceAugmentation_pushforwardIso J U a :=
  sorry
