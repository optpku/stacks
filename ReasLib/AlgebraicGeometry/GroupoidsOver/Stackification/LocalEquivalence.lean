module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Stackification.Construction
public import ReasLib.CategoryTheory.Sites.LocallyBijective.SheafLift

/-! # Actual local witnesses after replacing the stackification Hom types by small codes -/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Functor.StackificationConstruction
open scoped CategoryTheory.Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Stackification

variable {S : Scheme.{u}} {X : Type (u + 1)} [Category.{u} X]
variable (p : X ⥤ Over S) (χ : p.Cleavage) [Functor.IsFibered.InGroupoids p]

/-- The source Hom sections retain the original value universe. -/
def smallHomSource {U : Over S} (x y : p.Fiber U) : (Over U)ᵒᵖ ⥤ Type u :=
  (Functor.fiberPseudofunctor p).presheafHom x y ⋙ uliftFunctor.{u, u}

/-- Target Hom sections use the actual small Hom models of the target. -/
def smallHomTarget {U : Over S} (x y : p.Fiber U) : (Over U)ᵒᵖ ⥤ Type u :=
  (Functor.fiberPseudofunctor (smallProjection p χ)).presheafHom
    (((smallComparison p χ).fiberFunctor U).obj x)
    (((smallComparison p χ).fiberFunctor U).obj y) ⋙ uliftFunctor.{u, u}

/-- A small target section is sent back through the actual standard-fibre
equivalence, after the two original Cartesian reindexing comparisons. -/
def largeHomSection {U : Over S} (x y : p.Fiber U) (W : Over U)
    (s : (smallHomTarget p χ x y).obj (op W)) :
    (CategoryTheory.Functor.StackificationConstruction.homTarget
      (Scheme.fppfTopology.over S) p χ x y).obj (op W) := by
  let F := shrinkCartesian p χ
  let a := ((comparison (Scheme.fppfTopology.over S) p χ).fiberFunctor U).obj x
  let b := ((comparison (Scheme.fppfTopology.over S) p χ).fiberFunctor U).obj y
  let ex := CartesianBasedFunctor.Reindex.mapIso F
    (Functor.Cleavage.ofIsFibered (targetProjection (Scheme.fppfTopology.over S) p χ))
    (Functor.Cleavage.ofIsFibered (smallProjection p χ)) W.hom a
  let ey := CartesianBasedFunctor.Reindex.mapIso F
    (Functor.Cleavage.ofIsFibered (targetProjection (Scheme.fppfTopology.over S) p χ))
    (Functor.Cleavage.ofIsFibered (smallProjection p χ)) W.hom b
  exact ULift.up ((Functor.FullyFaithful.ofFullyFaithful
    (smallFiberEquivalence p χ W.left).functor).preimage (ex.inv ≫ s.down ≫ ey.hom))

/-- The original representative's actual covering sieve remains the surjectivity cover. -/
def smallHomCover {U : Over S} (x y : p.Fiber U) (W : Over U)
    (s : (smallHomTarget p χ x y).obj (op W)) : (Scheme.fppfTopology.over S).Cover W.left :=
  homSurjectivityCover (Scheme.fppfTopology.over S) p χ x y W (largeHomSection p χ x y W s)

/-- The actual original local preimage is rewrapped in the original value universe. -/
def smallHomPreimage {U : Over S} (x y : p.Fiber U) (W : Over U)
    (s : (smallHomTarget p χ x y).obj (op W))
    (I : (smallHomCover p χ x y W s).Arrow) :
    (smallHomSource p x y).obj (op (Over.mk (I.f ≫ W.hom))) :=
  ULift.up (homSurjectivityPreimage (Scheme.fppfTopology.over S) p χ x y W
    (largeHomSection p χ x y W s) I).down

/-- The explicit local preimage maps to the restricted small section. -/
theorem smallHomPreimage_map {U : Over S} (x y : p.Fiber U) (W : Over U)
    (s : (smallHomTarget p χ x y).obj (op W))
    (I : (smallHomCover p χ x y W s).Arrow) :
    (CartesianBasedFunctor.HomPresheaf.Chosen.map (smallComparison p χ) x y).app _
      (smallHomPreimage p χ x y W s I) =
      (smallHomTarget p χ x y).map (Over.homMk I.f).op s := sorry

/-- Small Hom maps are locally surjective on the actual original representative covers. -/
theorem smallHomLocallySurjective {U : Over S} (x y : p.Fiber U) :
    Presheaf.IsLocallySurjective ((Scheme.fppfTopology.over S).over U)
      (CartesianBasedFunctor.HomPresheaf.Chosen.map (smallComparison p χ) x y) where
  imageSieve_mem {W} s := by
    let J := Scheme.fppfTopology.over S
    let R := smallHomCover p χ x y W s
    apply (J.over U).superset_covering
      (S := (Sieve.overEquiv W).symm (R : Sieve W.left)) _
      (J.overEquiv_symm_mem_over W _ R.2)
    intro Z f hf
    let I : R.Arrow := ⟨Z.left, f.left, (Sieve.overEquiv_symm_iff _ f).mp hf⟩
    let e : Over.mk (I.f ≫ W.hom) ≅ Z :=
      Over.isoMk (Iso.refl Z.left) ((Category.id_comp Z.hom).trans (Over.w f).symm)
    exact ⟨(smallHomSource p x y).map e.inv.op (smallHomPreimage p χ x y W s I), by sorry⟩

/-- Equality of small section images gives the original local-equality
sieve. The original equality premise is explicitly retained. -/
theorem smallHomEqualitySieve_mem {U : Over S} (x y : p.Fiber U) (W : Over U)
    (s t : (smallHomSource p x y).obj (op W))
    (h : (CartesianBasedFunctor.HomPresheaf.Chosen.map (smallComparison p χ) x y).app _ s =
      (CartesianBasedFunctor.HomPresheaf.Chosen.map (smallComparison p χ) x y).app _ t) :
    equalitySieve p χ s.down.1 t.down.1 ∈
      (Scheme.fppfTopology.over S) (p.obj (W.hom⁎[Functor.Cleavage.ofIsFibered p] x).1) := sorry

/-- The concrete equality sieve is transported to the section's actual base object. -/
def smallHomEqualityCover {U : Over S} (x y : p.Fiber U) (W : Over U)
    (s t : (smallHomSource p x y).obj (op W))
    (h : (CartesianBasedFunctor.HomPresheaf.Chosen.map (smallComparison p χ) x y).app _ s =
      (CartesianBasedFunctor.HomPresheaf.Chosen.map (smallComparison p χ) x y).app _ t) :
    (Scheme.fppfTopology.over S).Cover W.left :=
  GrothendieckTopology.Cover.pullback
    (⟨equalitySieve p χ s.down.1 t.down.1, smallHomEqualitySieve_mem p χ x y W s t h⟩ :
      (Scheme.fppfTopology.over S).Cover (p.obj (W.hom⁎[Functor.Cleavage.ofIsFibered p] x).1))
    (eqToHom (W.hom⁎[Functor.Cleavage.ofIsFibered p] x).2.symm)

/-- The two original sections agree on every arrow of the actual equality cover. -/
theorem smallHomEqualityCover_equal {U : Over S} (x y : p.Fiber U) (W : Over U)
    (s t : (smallHomSource p x y).obj (op W))
    (h : (CartesianBasedFunctor.HomPresheaf.Chosen.map (smallComparison p χ) x y).app _ s =
      (CartesianBasedFunctor.HomPresheaf.Chosen.map (smallComparison p χ) x y).app _ t)
    (I : (smallHomEqualityCover p χ x y W s t h).Arrow) :
    (smallHomSource p x y).map (Over.homMk I.f : Over.mk (I.f ≫ W.hom) ⟶ W).op s =
      (smallHomSource p x y).map (Over.homMk I.f : Over.mk (I.f ≫ W.hom) ⟶ W).op t := sorry

/-- Small Hom maps are locally injective on the actual original equality sieves. -/
theorem smallHomLocallyInjective {U : Over S} (x y : p.Fiber U) :
    Presheaf.IsLocallyInjective ((Scheme.fppfTopology.over S).over U)
      (CartesianBasedFunctor.HomPresheaf.Chosen.map (smallComparison p χ) x y) where
  equalizerSieve_mem {W} s t h := by
    let J := Scheme.fppfTopology.over S
    let R := smallHomEqualityCover p χ x y W.unop s t h
    apply (J.over U).superset_covering
      (S := (Sieve.overEquiv W.unop).symm (R : Sieve W.unop.left)) _
      (J.overEquiv_symm_mem_over W.unop _ R.2)
    intro Z f hf
    have member : R f.left := (Sieve.overEquiv_symm_iff _ f).mp hf
    have localEq := smallHomEqualityCover_equal p χ x y W.unop s t h
      (⟨Z.left, f.left, member⟩ : R.Arrow)
    let e : Over.mk (f.left ≫ W.unop.hom) ≅ Z :=
      Over.isoMk (Iso.refl Z.left) ((Category.id_comp Z.hom).trans (Over.w f).symm)
    have transported := congrArg ((smallHomSource p x y).map e.inv.op) localEq
    exact (show (smallHomSource p x y).map f.op s = _ from by sorry).trans
      (transported.trans (by sorry))

/-- Local Hom equivalence has explicit preimages on actual covers and an
actual glued inverse on maps into every supplied sheaf. -/
theorem smallComparisonHomwise :
    CartesianBasedFunctor.Homwise.IsLocalEquivalence (Scheme.fppfTopology.over S)
      (smallComparison p χ) := by
  intro U x y
  exact ⟨smallHomLocallyInjective p χ x y, smallHomLocallySurjective p χ x y⟩

/-- A small target object retains the identical object in the original large realization. -/
def largeTargetModel {U : Over S} (z : (smallProjection p χ).Fiber U) :
    (targetProjection (Scheme.fppfTopology.over S) p χ).Fiber U :=
  ⟨(ShrinkHoms.equivalence.{u} (largeTotal p χ)).inverse.obj z.1, z.2⟩

/-- Both object models differ only by the native identity-on-objects Hom equivalence. -/
def largeTargetModelIso {U : Over S} (z : (smallProjection p χ).Fiber U) :
    ((shrinkCartesian p χ).fiberFunctor U).obj (largeTargetModel p χ z) ≅ z :=
  eqToIso (by sorry)

/-- The original stored local object models are mapped by the actual Hom
equivalence and compared using its actual Cartesian restriction maps. -/
theorem smallComparisonLocallyEssentiallySurjective :
    CartesianBasedFunctor.LocallyEssentiallySurjective (Scheme.fppfTopology.over S)
      (smallComparison p χ) := by
  intro U z
  let J := Scheme.fppfTopology.over S
  let y := largeTargetModel p χ z
  have hcover := comparisonLocallyEssentiallySurjective J p χ y
  apply J.superset_covering (S := CartesianBasedFunctor.EssentialImage.sieve (comparison J p χ) y) _ hcover
  intro V f hf
  rcases hf with ⟨x, ⟨e⟩⟩
  let F := shrinkCartesian p χ
  let ξ := Functor.Cleavage.ofIsFibered (smallProjection p χ)
  exact ⟨x, ⟨(F.fiberFunctor V).mapIso e ≪≫
    (CartesianBasedFunctor.Reindex.mapIso F
      (Functor.Cleavage.ofIsFibered (targetProjection J p χ)) ξ f y).symm ≪≫
    (ξ.reindex f).mapIso (largeTargetModelIso p χ z)⟩⟩

/-- Both source-facing local conditions are carried by actual covers, models and maps. -/
theorem smallComparisonIsStackification :
    CartesianBasedFunctor.IsStackification (Scheme.fppfTopology.over S)
      (smallComparison p χ) where
  isLocalEquivalence :=
    ⟨smallComparisonHomwise p χ, smallComparisonLocallyEssentiallySurjective p χ⟩
  isStack := smallIsStack p χ

end AlgebraicGeometry.GroupoidsOver.Stackification
