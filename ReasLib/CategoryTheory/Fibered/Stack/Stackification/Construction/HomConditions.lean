module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.LocalConditions
public import ReasLib.CategoryTheory.Sites.TypeSheafification

/-!
# Actual local preimages for the comparison Hom presheaves

Local surjectivity uses the stored representative cover and original Cartesian
factors. Local injectivity uses the original local-equality sieve.
-/

@[expose] public section

open CategoryTheory Opposite GrothendieckTopology
open scoped CategoryTheory.Bicategory

noncomputable section

universe u v uX vX

namespace CategoryTheory.Functor.StackificationConstruction

variable {C : Type u} [Category.{v} C] {X : Type uX} [Category.{vX} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C) (χ : p.Cleavage) [p.IsFibered]

/-- The original Hom presheaf in the universe required by both projections. -/
def homSource {U : C} (x y : p.Fiber U) : (Over U)ᵒᵖ ⥤ Type (max u v vX) :=
  (fiberPseudofunctor p).presheafHom x y ⋙ uliftFunctor.{max u v vX, vX}

/-- The target Hom presheaf at the actual comparison images. -/
def homTarget {U : C} (x y : p.Fiber U) : (Over U)ᵒᵖ ⥤ Type (max u v vX) :=
  (fiberPseudofunctor (targetProjection J p χ)).presheafHom
    (((comparison J p χ).fiberFunctor U).obj x)
    (((comparison J p χ).fiberFunctor U).obj y) ⋙
      uliftFunctor.{max u v vX, max u v vX}

/-- Move a target section to the images of the original restricted objects
using the actual Cartesian reindexing comparison in both directions. -/
def homSection {U : C} (x y : p.Fiber U) (W : Over U)
    (s : (homTarget J p χ x y).obj (op W)) :
    ((comparison J p χ).fiberFunctor W.left).obj
      (W.hom⁎[Cleavage.ofIsFibered p] x) ⟶
    ((comparison J p χ).fiberFunctor W.left).obj
      (W.hom⁎[Cleavage.ofIsFibered p] y) :=
  (CartesianBasedFunctor.Reindex.mapIso (comparison J p χ)
    (Cleavage.ofIsFibered p) (Cleavage.ofIsFibered (targetProjection J p χ)) W.hom x).inv ≫
    s.down ≫
    (CartesianBasedFunctor.Reindex.mapIso (comparison J p χ)
      (Cleavage.ofIsFibered p) (Cleavage.ofIsFibered (targetProjection J p χ)) W.hom y).hom

/-- A target section yields its actual original local-arrow preimage. -/
def homSectionLocal {U : C} (x y : p.Fiber U) (W : Over U)
    (s : (homTarget J p χ x y).obj (op W)) :
    ((Localized.comparison J p χ).fiberFunctor W.left).obj
      (W.hom⁎[Cleavage.ofIsFibered p] x) ⟶
    ((Localized.comparison J p χ).fiberFunctor W.left).obj
      (W.hom⁎[Cleavage.ofIsFibered p] y) :=
  localizedPreimage J p χ _ _ (homSection J p χ x y W s)

/-- The local surjectivity cover is the original representative's stored cover. -/
def homSurjectivityCover {U : C} (x y : p.Fiber U) (W : Over U)
    (s : (homTarget J p χ x y).obj (op W)) : J.Cover W.left :=
  homLocalCover J p χ (homSectionLocal J p χ x y W s)

/-- A local preimage over the composite slice arrow uses the actual original
Cartesian factors and the original cleavage composition comparison. -/
def homSurjectivityPreimage {U : C} (x y : p.Fiber U) (W : Over U)
    (s : (homTarget J p χ x y).obj (op W))
    (I : (homSurjectivityCover J p χ x y W s).Arrow) :
    (homSource p x y).obj (op (Over.mk (I.f ≫ W.hom))) :=
  ULift.up (
    (Cleavage.Reindex.compIsoApp (Cleavage.ofIsFibered p) W.hom I.f x).hom ≫
    homLocalPreimageWith J p χ (Cleavage.ofIsFibered p)
      (homSectionLocal J p χ x y W s) I ≫
    (Cleavage.Reindex.compIsoApp (Cleavage.ofIsFibered p) W.hom I.f y).inv)

/-- The explicit local preimage maps to the corresponding restricted section. -/
theorem homSurjectivityPreimage_map {U : C} (x y : p.Fiber U) (W : Over U)
    (s : (homTarget J p χ x y).obj (op W))
    (I : (homSurjectivityCover J p χ x y W s).Arrow) :
    (CartesianBasedFunctor.HomPresheaf.Chosen.map (comparison J p χ) x y).app _
      (homSurjectivityPreimage J p χ x y W s I) =
      (homTarget J p χ x y).map (Over.homMk I.f).op s := sorry

/-- The Hom comparison is locally surjective using the stored representative
cover and the explicit original preimages on every covering arrow. -/
theorem homMapLocallySurjective {U : C} (x y : p.Fiber U) :
    Presheaf.IsLocallySurjective (J.over U)
      (CartesianBasedFunctor.HomPresheaf.Chosen.map (comparison J p χ) x y) where
  imageSieve_mem {W} s := by
    let R := homSurjectivityCover J p χ x y W s
    apply (J.over U).superset_covering
      (S := (Sieve.overEquiv W).symm (R : Sieve W.left)) _
      (J.overEquiv_symm_mem_over W _ R.2)
    intro Z f hf
    let I : R.Arrow := ⟨Z.left, f.left, (Sieve.overEquiv_symm_iff _ f).mp hf⟩
    let e : Over.mk (I.f ≫ W.hom) ≅ Z :=
      Over.isoMk (Iso.refl Z.left) ((Category.id_comp Z.hom).trans (Over.w f).symm)
    exact ⟨(homSource p x y).map e.inv.op
      (homSurjectivityPreimage J p χ x y W s I), by sorry⟩

/-- Equality of comparison images is exactly local equality of original
arrows: native realization and the prestack unit are faithful, and the
local-arrow inclusion reflects the separated quotient relation. -/
theorem comparisonFiber_localEquality {V : C} {x y : p.Fiber V}
    (δ ε : x ⟶ y)
    (h : ((comparison J p χ).fiberFunctor V).map δ =
      ((comparison J p χ).fiberFunctor V).map ε) :
    LocallyEqual J p χ δ.1 ε.1 := sorry

/-- Equal Hom-map images give the original equality sieve as a covering sieve. -/
theorem homSection_imageEquality {U : C} (x y : p.Fiber U) (W : Over U)
    (s t : (homSource p x y).obj (op W))
    (h : (CartesianBasedFunctor.HomPresheaf.Chosen.map (comparison J p χ) x y).app _ s =
      (CartesianBasedFunctor.HomPresheaf.Chosen.map (comparison J p χ) x y).app _ t) :
    ((comparison J p χ).fiberFunctor W.left).map s.down =
      ((comparison J p χ).fiberFunctor W.left).map t.down := sorry

/-- The original image-equality premise is explicitly retained when reflecting
the completed Hom comparison to the original local-equality sieve. -/
theorem homEqualitySieve_mem {U : C} (x y : p.Fiber U) (W : Over U)
    (s t : (homSource p x y).obj (op W))
    (h : (CartesianBasedFunctor.HomPresheaf.Chosen.map (comparison J p χ) x y).app _ s =
      (CartesianBasedFunctor.HomPresheaf.Chosen.map (comparison J p χ) x y).app _ t) :
    equalitySieve p χ s.down.1 t.down.1 ∈
      J (p.obj (W.hom⁎[Cleavage.ofIsFibered p] x).1) :=
  (comparisonFiber_localEquality J p χ s.down t.down
    (homSection_imageEquality J p χ x y W s t h)).2

/-- The injectivity cover is the explicit original equality sieve, transported
to the section's actual fibre index. -/
def homInjectivityCover {U : C} (x y : p.Fiber U) (W : Over U)
    (s t : (homSource p x y).obj (op W))
    (h : (CartesianBasedFunctor.HomPresheaf.Chosen.map (comparison J p χ) x y).app _ s =
      (CartesianBasedFunctor.HomPresheaf.Chosen.map (comparison J p χ) x y).app _ t) :
    J.Cover W.left :=
  Cover.pullback
    (⟨equalitySieve p χ s.down.1 t.down.1, homEqualitySieve_mem J p χ x y W s t h⟩ :
      J.Cover (p.obj (W.hom⁎[Cleavage.ofIsFibered p] x).1))
    (eqToHom (W.hom⁎[Cleavage.ofIsFibered p] x).2.symm)

/-- The stored equality condition says the two original sections agree on
every arrow of the explicit local equality cover. -/
theorem homInjectivityCover_equal {U : C} (x y : p.Fiber U) (W : Over U)
    (s t : (homSource p x y).obj (op W))
    (h : (CartesianBasedFunctor.HomPresheaf.Chosen.map (comparison J p χ) x y).app _ s =
      (CartesianBasedFunctor.HomPresheaf.Chosen.map (comparison J p χ) x y).app _ t)
    (I : (homInjectivityCover J p χ x y W s t h).Arrow) :
    (homSource p x y).map (Over.homMk I.f : Over.mk (I.f ≫ W.hom) ⟶ W).op s =
      (homSource p x y).map (Over.homMk I.f : Over.mk (I.f ≫ W.hom) ⟶ W).op t := sorry

/-- The Hom comparison is locally injective on the actual original equality sieve. -/
theorem homMapLocallyInjective {U : C} (x y : p.Fiber U) :
    Presheaf.IsLocallyInjective (J.over U)
      (CartesianBasedFunctor.HomPresheaf.Chosen.map (comparison J p χ) x y) where
  equalizerSieve_mem {W} s t h := by
    let R := homInjectivityCover J p χ x y W.unop s t h
    apply (J.over U).superset_covering
      (S := (Sieve.overEquiv W.unop).symm (R : Sieve W.unop.left)) _
      (J.overEquiv_symm_mem_over W.unop _ R.2)
    intro Z f hf
    have member : R f.left := (Sieve.overEquiv_symm_iff _ f).mp hf
    have localEq := homInjectivityCover_equal J p χ x y W.unop s t h
      (⟨Z.left, f.left, member⟩ : R.Arrow)
    let e : Over.mk (f.left ≫ W.unop.hom) ≅ Z :=
      Over.isoMk (Iso.refl Z.left) ((Category.id_comp Z.hom).trans (Over.w f).symm)
    have transported := congrArg ((homSource p x y).map e.inv.op) localEq
    exact (show (homSource p x y).map f.op s = _ from by sorry).trans
      (transported.trans (by sorry))

/-- Both local Hom conditions retain their actual covers and original preimages. -/
theorem comparisonHomwise :
    CartesianBasedFunctor.Homwise.IsLocalEquivalence J (comparison J p χ) := by
  intro U x y
  exact ⟨homMapLocallyInjective J p χ x y, homMapLocallySurjective J p χ x y⟩

/-- The concrete comparison is locally fully faithful and locally essentially surjective. -/
theorem comparisonIsLocalEquivalence :
    CartesianBasedFunctor.IsLocalEquivalence J (comparison J p χ) :=
  ⟨comparisonHomwise J p χ, comparisonLocallyEssentiallySurjective J p χ⟩

end CategoryTheory.Functor.StackificationConstruction
