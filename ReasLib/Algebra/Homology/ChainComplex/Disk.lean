module

public import ReasLib.Algebra.Homology.ChainComplex.TwoTerm
public import ReasLib.CategoryTheory.NatTrans.Arrow
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Disk chain complexes

The disk complex on `A` in degree `k` is the specialization of `ChainComplex.twoTerm` to
`𝟙 A`. This file exposes the representation-independent endpoint, differential, functorial,
splitting, and exactness API of that specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

universe v u

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The disk complex on `A`, with identity differential from degree `k + 1` to degree `k`. -/
@[stacks 0192 "disk chain complex"]
noncomputable abbrev disk (A : C) (k : ℕ) : ChainComplex C ℕ :=
  twoTerm (𝟙 A) k

namespace disk

/-- The canonical identification of the upper term of a disk complex with its coefficient
object. -/
@[stacks 0192 "upper term of a disk chain complex"]
noncomputable abbrev upperIso (A : C) (k : ℕ) :
    (disk A k).X (k + 1) ≅ A :=
  twoTerm.upperIso (𝟙 A) k

/-- The canonical identification of the lower term of a disk complex with its coefficient
object. -/
@[stacks 0192 "lower term of a disk chain complex"]
noncomputable abbrev lowerIso (A : C) (k : ℕ) :
    (disk A k).X k ≅ A :=
  twoTerm.lowerIso (𝟙 A) k

/-- The unique nonzero differential of a disk complex is the identity under its endpoint
identifications. -/
@[simp, stacks 0192 "differential of a disk chain complex"]
theorem d (A : C) (k : ℕ) :
    (disk A k).d (k + 1) k =
      (upperIso A k).hom ≫ (lowerIso A k).inv := sorry

/-- Every term outside degrees `k + 1` and `k` in a disk complex is zero. -/
@[stacks 0192 "vanishing outside a disk chain complex"]
theorem isZero_X (A : C) (k n : ℕ) (hUpper : n ≠ k + 1) (hLower : n ≠ k) :
    IsZero ((disk A k).X n) := sorry

/-- A coefficient morphism induces the componentwise map of disk complexes. -/
@[stacks 0192 "map of disk chain complexes"]
noncomputable abbrev map (k : ℕ) {A B : C} (f : A ⟶ B) :
    disk A k ⟶ disk B k :=
  twoTerm.map ((𝟙 (𝟭 C) : 𝟭 C ⟶ 𝟭 C).arrowFunctor.map f) k

namespace map

/-- The upper component of a disk map is the coefficient morphism under the canonical endpoint
identifications. -/
@[simp, stacks 0192 "upper component of a disk map"]
theorem upper (k : ℕ) {A B : C} (f : A ⟶ B) :
    (map k f).f (k + 1) =
      (upperIso A k).hom ≫ f ≫ (upperIso B k).inv := sorry

/-- The lower component of a disk map is the coefficient morphism under the canonical endpoint
identifications. -/
@[simp, stacks 0192 "lower component of a disk map"]
theorem lower (k : ℕ) {A B : C} (f : A ⟶ B) :
    (map k f).f k =
      (lowerIso A k).hom ≫ f ≫ (lowerIso B k).inv := sorry

/-- Mapping an identity gives the identity of the disk complex. -/
theorem id (k : ℕ) (A : C) : map k (𝟙 A) = 𝟙 (disk A k) := sorry

/-- Disk-complex maps preserve composition. -/
theorem comp (k : ℕ) {A B D : C} (f : A ⟶ B) (g : B ⟶ D) :
    map k (f ≫ g) = map k f ≫ map k g := sorry

end map

/-- Disk complexes form a functor of their coefficient object. -/
@[stacks 0192 "disk chain complex functor"]
noncomputable abbrev functor (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [HasZeroObject C] (k : ℕ) : C ⥤ ChainComplex C ℕ :=
  (𝟙 (𝟭 C) : 𝟭 C ⟶ 𝟭 C).arrowFunctor ⋙ twoTerm.functor C k

/-- The disk functor evaluates to `disk A k`. -/
@[simp, stacks 0192 "disk functor object formula"]
theorem functor_obj (k : ℕ) (A : C) :
    (functor C k).obj A = disk A k := sorry

/-- The disk functor maps a coefficient morphism by `disk.map`. -/
@[simp, stacks 0192 "disk functor map formula"]
theorem functor_map (k : ℕ) {A B : C} (f : A ⟶ B) :
    (functor C k).map f = map k f := sorry

/-- The canonical inclusion of the lower single complex into a disk complex. -/
@[stacks 0192 "lower single-complex inclusion into a disk complex"]
noncomputable abbrev ιApp (A : C) (k : ℕ) :
    (single C (ComplexShape.down ℕ) k).obj A ⟶ disk A k :=
  twoTerm.ιApp (Arrow.mk (𝟙 A)) k

namespace ι

/-- The lower single-complex inclusions are natural in the coefficient object. -/
theorem naturality {A B : C} (f : A ⟶ B) (k : ℕ) :
    (single C (ComplexShape.down ℕ) k).map f ≫ ιApp B k =
      ιApp A k ≫ (functor C k).map f := sorry

end ι

/-- The inclusions of lower single complexes form a natural transformation into the disk
functor. -/
@[stacks 0192 "natural lower single-complex inclusion into disk complexes"]
noncomputable def ι (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [HasZeroObject C] (k : ℕ) :
    single C (ComplexShape.down ℕ) k ⟶ functor C k where
  app A := ιApp A k
  naturality _ _ f := ι.naturality f k

/-- The component of the natural disk inclusion is `ιApp`. -/
@[simp, stacks 0192 "disk inclusion component formula"]
theorem ι_app (k : ℕ) (A : C) : (ι C k).app A = ιApp A k := sorry

/-- The canonical projection from a disk complex onto the upper single complex. -/
@[stacks 0192 "upper single-complex projection from a disk complex"]
noncomputable abbrev πApp (A : C) (k : ℕ) :
    disk A k ⟶ (single C (ComplexShape.down ℕ) (k + 1)).obj A :=
  twoTerm.πApp (Arrow.mk (𝟙 A)) k

namespace π

/-- The upper single-complex projections are natural in the coefficient object. -/
theorem naturality {A B : C} (f : A ⟶ B) (k : ℕ) :
    (functor C k).map f ≫ πApp B k =
      πApp A k ≫ (single C (ComplexShape.down ℕ) (k + 1)).map f := sorry

end π

/-- The projections onto upper single complexes form a natural transformation out of the disk
functor. -/
@[stacks 0192 "natural upper single-complex projection from disk complexes"]
noncomputable def π (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [HasZeroObject C] (k : ℕ) :
    functor C k ⟶ single C (ComplexShape.down ℕ) (k + 1) where
  app A := πApp A k
  naturality _ _ f := π.naturality f k

/-- The component of the natural disk projection is `πApp`. -/
@[simp, stacks 0192 "disk projection component formula"]
theorem π_app (k : ℕ) (A : C) : (π C k).app A = πApp A k := sorry

/-- The natural inclusion and projection of disk complexes compose to zero. -/
@[stacks 0192 "single-disk-single composition"]
theorem ι_comp_π (k : ℕ) : ι C k ≫ π C k = 0 := sorry

/-- The canonical single--disk--single short complex, functorial in the coefficient object. -/
@[stacks 0192 "functorial single-disk-single short complex"]
noncomputable def shortComplex (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [HasZeroObject C] (k : ℕ) : ShortComplex (C ⥤ ChainComplex C ℕ) :=
  ShortComplex.mk (ι C k) (π C k) (ι_comp_π k)

namespace shortComplex

/-- Evaluate the functorial single--disk--single row at a coefficient object. -/
@[stacks 0192 "single-disk-single short complex at a coefficient object"]
abbrev app (A : C) (k : ℕ) : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.FunctorCategory.app (shortComplex C k) A

end shortComplex

end disk

section Splitting

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace disk.degree

/-- The degreewise retraction from a disk complex onto its lower single summand. -/
@[stacks 0192 "degreewise retraction of a disk complex"]
noncomputable abbrev retraction (A : C) (k n : ℕ) :
    (disk A k).X n ⟶ ((single C (ComplexShape.down ℕ) k).obj A).X n :=
  twoTerm.degree.retraction (Arrow.mk (𝟙 A)) k n

/-- The degreewise section of the upper single quotient into a disk complex. -/
@[stacks 0192 "degreewise section of a disk complex"]
noncomputable abbrev section_ (A : C) (k n : ℕ) :
    ((single C (ComplexShape.down ℕ) (k + 1)).obj A).X n ⟶ (disk A k).X n :=
  twoTerm.degree.section_ (Arrow.mk (𝟙 A)) k n

namespace laws

/-- The degreewise retraction is a right inverse to the disk inclusion. -/
theorem f_r (A : C) (k n : ℕ) :
    ((disk.shortComplex.app A k).degreewise n).f ≫ retraction A k n = 𝟙 _ := sorry

/-- The degreewise section is a left inverse to the disk projection. -/
theorem s_g (A : C) (k n : ℕ) :
    section_ A k n ≫ ((disk.shortComplex.app A k).degreewise n).g = 𝟙 _ := sorry

/-- The degreewise retraction and section split the identity of the disk term. -/
theorem id (A : C) (k n : ℕ) :
    (retraction A k n ≫
        (((disk.shortComplex.app A k).degreewise n).f :
          ((single C (ComplexShape.down ℕ) k).obj A).X n ⟶ (disk A k).X n) :
        (disk A k).X n ⟶ (disk A k).X n) +
      ((((disk.shortComplex.app A k).degreewise n).g :
          (disk A k).X n ⟶
            ((single C (ComplexShape.down ℕ) (k + 1)).obj A).X n) ≫
        section_ A k n : (disk A k).X n ⟶ (disk A k).X n) = 𝟙 _ := sorry

end laws

/-- The explicit splitting of the single--disk--single row in chain degree `n`. -/
@[stacks 0192 "degreewise splitting of a disk complex"]
noncomputable def splitting (A : C) (k n : ℕ) :
    ((disk.shortComplex.app A k).degreewise n).Splitting where
  r := retraction A k n
  s := section_ A k n
  f_r := laws.f_r A k n
  s_g := laws.s_g A k n
  id := laws.id A k n

end disk.degree

/-- The chosen degreewise splitting of the single--disk--single row. -/
@[stacks 0192 "chosen degreewise splitting of a disk complex"]
noncomputable def disk.degreewiseSplitting (A : C) (k : ℕ) :
    ShortComplex.DegreewiseSplitting (disk.shortComplex.app A k) :=
  fun n ↦ disk.degree.splitting A k n

/-- The single--disk--single row is degreewise split. -/
@[stacks 0192 "degreewise-split disk complex row"]
theorem disk.isDegreewiseSplit (A : C) (k : ℕ) :
    (disk.shortComplex.app A k).IsDegreewiseSplit := sorry

/-- Every disk complex is acyclic. -/
@[stacks 0192 "acyclic disk chain complex"]
theorem disk.acyclic (A : C) (k : ℕ) : (disk A k).Acyclic := sorry

end Splitting

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical single--disk--single row is short exact in an abelian category. -/
@[stacks 0192 "short exact single-disk-single row"]
theorem disk.shortComplex.app.shortExact (A : C) (k : ℕ) :
    (disk.shortComplex.app A k).ShortExact := sorry

end Abelian

end ChainComplex
