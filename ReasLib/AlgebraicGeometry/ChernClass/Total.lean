module

public import Mathlib.RingTheory.PowerSeries.Basic
public import ReasLib.AlgebraicGeometry.ChernClass.Theory
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w x

namespace AlgebraicGeometry.ChernClass

/-- The vector bundle represented by a Picard class. -/
noncomputable def picardVectorBundle (X : Scheme.{u}) (L : X.PicardGroup) :
    ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) :=
  ⟨Scheme.PicardGroup.repr L,
    @Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
      X 1 (Scheme.PicardGroup.repr L)
      (@Scheme.Modules.isFiniteLocallyFreeOfRankOne_of_invertible
        X inferInstance (Scheme.PicardGroup.repr L) inferInstance)⟩

/-- The underlying module of the vector bundle represented by a Picard class is its canonical
representative. -/
theorem picardVectorBundle_obj (X : Scheme.{u}) (L : X.PicardGroup) :
    (picardVectorBundle X L).obj = Scheme.PicardGroup.repr L := sorry

/-- The class in `K₀(Vect(X))` of the invertible module represented by a Picard class. -/
noncomputable def picardK0Class (X : Scheme.{u}) (L : X.PicardGroup) :
    Scheme.VectorBundleK0 X :=
  ObjectProperty.GrothendieckGroup.of
    (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
    (picardVectorBundle X L)

/-- The `K₀` class of a Picard class is represented by its canonical invertible module. -/
theorem picardK0Class_eq (X : Scheme.{u}) (L : X.PicardGroup) :
    picardK0Class X L =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
        (picardVectorBundle X L) := sorry

/-- A total Chern class with values in the product of the homogeneous pieces of a graded
cohomology ring. The coefficient condition realizes that product inside power series. -/
structure TotalChernClass
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
    (A : Cᵒᵖ ⥤ RingCat.{x})
    (Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X)))
    (firstChernClass : ∀ X, (toScheme.obj X).PicardGroup →+ Agrade X 1) where
  /-- The total Chern class on the vector-bundle Grothendieck group. -/
  app : ∀ X, Scheme.VectorBundleK0 (toScheme.obj X) →
    PowerSeries (A.obj (Opposite.op X))
  /-- Total Chern classes turn addition in `K₀` into multiplication. -/
  map_add : ∀ X (alpha beta : Scheme.VectorBundleK0 (toScheme.obj X)),
    app X (alpha + beta) = app X alpha * app X beta
  /-- The zero `K₀`-class has total Chern class one. -/
  map_zero : ∀ X, app X 0 = 1
  /-- The coefficient of degree `i` belongs to the degree-`i` part of cohomology. -/
  coeff_mem : ∀ X (alpha : Scheme.VectorBundleK0 (toScheme.obj X)) (i : ℕ),
    PowerSeries.coeff i (app X alpha) ∈ Agrade X i
  /-- Total Chern classes commute with pullback. -/
  naturality : ∀ {X' X : C} (f : X' ⟶ X)
      (alpha : Scheme.VectorBundleK0 (toScheme.obj X)),
    PowerSeries.map (A.map f.op).hom (app X alpha) =
      app X' (Scheme.VectorBundleK0.pullback (toScheme.map f) alpha)
  /-- On a Picard class `L`, the total class is `1 + c₁(L)`. -/
  lineBundle : ∀ (X : C) (L : (toScheme.obj X).PicardGroup),
    app X (picardK0Class (toScheme.obj X) L) =
      1 + PowerSeries.monomial 1
        (firstChernClass X L : A.obj (Opposite.op X))

/-- A graded cohomology theory satisfying the Chern-class axioms has a unique total Chern class
on the Grothendieck groups of finite locally free modules. -/
theorem existsUniqueTotalChernClass
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
    (A : Cᵒᵖ ⥤ RingCat.{x})
    (Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X)))
    [∀ X, GradedAlgebra (Agrade X)] (S : CohomologyTheory toScheme A Agrade) :
    ∃ c : TotalChernClass toScheme A Agrade S.firstChernClass,
      ∀ c', c' = c := sorry

end AlgebraicGeometry.ChernClass
