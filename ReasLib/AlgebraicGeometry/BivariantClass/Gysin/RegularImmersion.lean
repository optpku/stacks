module

public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.NormalSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Dual
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Gysin

open Scheme.Hom Scheme.Hom.VirtualNormalBundle

/-- The conormal sheaf of a regular immersion is finite locally free. -/
@[instance]
theorem conormalSheaf_isFiniteLocallyFree {X P : Scheme.{u}}
    (i : X ⟶ P) [IsRegularImmersion i] :
    Scheme.Modules.IsFiniteLocallyFree (conormalSheaf i) := sorry

/-- The normal sheaf of a regular immersion is finite locally free. -/
@[instance]
theorem normalSheaf_isFiniteLocallyFree {X P : Scheme.{u}}
    (i : X ⟶ P) [IsRegularImmersion i] :
    Scheme.Modules.IsFiniteLocallyFree (normalSheaf i) := by
  apply (SheafOfModules.IsFiniteLocallyFree.iff_of_iso
    ((CategoryTheory.ihom (conormalSheaf i)).mapIso
      (RingedSpace.unitIsoTensorUnit X.toRingedSpace))).mpr
  exact @Scheme.Modules.IsFiniteLocallyFree.dual X (conormalSheaf i)
    (conormalSheaf_isFiniteLocallyFree i)

/-- The normal sheaf with its bidual identification is a virtual normal bundle, without
any assumption of globally constant rank. -/
def normalBundle {X P : Scheme.{u}} (i : X ⟶ P) [IsRegularImmersion i]
    (e : Scheme.Modules.dual (normalSheaf i) ≅ conormalSheaf i) :
    VirtualNormalBundle i :=
  ofSurjection i (normalSheaf i) (normalSheaf_isFiniteLocallyFree i) e.hom inferInstance

/-- The module of the normal virtual bundle is the normal sheaf. -/
theorem normalBundle_module {X P : Scheme.{u}} (i : X ⟶ P) [IsRegularImmersion i]
    (e : Scheme.Modules.dual (normalSheaf i) ≅ conormalSheaf i) :
    (normalBundle i e).module = normalSheaf i := rfl

/-- The quotient map of the normal virtual bundle is the chosen bidual identification. -/
theorem normalBundle_map {X P : Scheme.{u}} (i : X ⟶ P) [IsRegularImmersion i]
    (e : Scheme.Modules.dual (normalSheaf i) ≅ conormalSheaf i) :
    (normalBundle i e).map = e.hom := rfl

/-- The degree-`r` Gysin coefficient of a regular immersion is the normal-sheaf class of
its canonical closed factor followed by degree-zero open flat pullback. -/
def immersionClassDegree
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (i : X ⟶ P) [IsRegularImmersion i.left]
    (e : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left)
    (D : ClosedDeformation X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder
      (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
      (normalBundle i.left e).toCoborder)
    (r : ℕ) : BivariantClass δ i (r : ℤ) := by
  have c := comp δ
    (overHom X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i))
    (overHom (i.left.coborderRange.ι ≫ P.hom) P.hom i.left.coborderRange.ι rfl)
    (globalClassOfRank δ X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder
      (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
      (normalBundle i.left e).toCoborder D r)
    (@flatPullback _ _ δ _ _ _ _ _
      (overHom (i.left.coborderRange.ι ≫ P.hom) P.hom i.left.coborderRange.ι rfl) 0
      (by change Flat i.left.coborderRange.ι; infer_instance)
      (relativeDimension_zero_of_isOpenImmersion i.left.coborderRange.ι))
  have hcomp : overHom X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder
      (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i) ≫
      overHom (i.left.coborderRange.ι ≫ P.hom) P.hom i.left.coborderRange.ι rfl = i := by
    calc
      _ = overHom X.hom P.hom i.left (Over.w i) := by
        apply Over.OverMorphism.ext
        exact i.left.liftCoborder_ι
      _ = i := by
        unfold overHom
        exact Over.homMk_eta i (Over.w i)
  rw [hcomp] at c
  simp only [Nat.cast_zero, neg_zero, add_zero] at c
  convert c using 0
  rfl

/-- Restricting an immersion coefficient to its rank locus gives the composition of the
closed rank class with the degree-zero open pullback. -/
theorem immersionClassDegree_component
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
    (i : X ⟶ P) [IsRegularImmersion i.left]
    (e : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left)
    (D : ClosedDeformation X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder
      (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
      (normalBundle i.left e).toCoborder)
    (r : ℕ) :
    ComponentRestriction.restrict δ i (r : ℤ)
        (rankOpen i.left (normalBundle i.left e) r) ⊤ (by simp)
        (immersionClassDegree δ i e D r) =
      (by
        have c := comp δ
          (ClosedDeformation.rankHom X.hom (i.left.coborderRange.ι ≫ P.hom)
            i.left.liftCoborder
            (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
            (normalBundle i.left e).toCoborder r)
          (ComponentRestriction.hom
            (overHom (i.left.coborderRange.ι ≫ P.hom) P.hom i.left.coborderRange.ι rfl)
            ⊤ ⊤ (by simp))
          (closedClassOfRank δ X.hom (i.left.coborderRange.ι ≫ P.hom)
            i.left.liftCoborder
      (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
      (normalBundle i.left e).toCoborder D r)
          (ComponentRestriction.restrict δ
            (overHom (i.left.coborderRange.ι ≫ P.hom) P.hom i.left.coborderRange.ι rfl)
            0 ⊤ ⊤ (by simp)
            (@flatPullback _ _ δ _ _ _ _ _
              (overHom (i.left.coborderRange.ι ≫ P.hom) P.hom i.left.coborderRange.ι rfl) 0
              (by change Flat i.left.coborderRange.ι; infer_instance)
              (relativeDimension_zero_of_isOpenImmersion i.left.coborderRange.ι)))
        dsimp only [ClosedDeformation.rankHom, VirtualNormalBundle.toCoborder] at c
        rw [factorizationRestrictionHom_eq X.hom P.hom i.left (Over.w i)
          i.left.liftCoborder i.left.coborderRange.ι i.left.liftCoborder_ι
          (normalBundle i.left e) r, add_zero] at c
        have h : overHom X.hom P.hom i.left (Over.w i) = i := by
          unfold overHom
          exact Over.homMk_eta i (Over.w i)
        rw [h] at c
        convert c using 0
        rfl) := sorry

end AlgebraicGeometry.BivariantClass.Gysin
