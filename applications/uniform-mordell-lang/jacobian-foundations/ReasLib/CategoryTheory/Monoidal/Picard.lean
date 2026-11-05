module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import ReasLib.CategoryTheory.Monoidal.Invertible.Duality
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Picard groups of monoidal categories

The Picard group of a monoidal category is the additive group of tensor-invertible
isomorphism classes.  Following `CommRing.Pic`, the representation is the group of units of the
monoid on the skeleton.  Braiding is needed only to make this group commutative.
-/

@[expose] public section

noncomputable section

universe v u v' u' v'' u''

namespace CategoryTheory.MonoidalCategory

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- The Picard group of a monoidal category, written additively. -/
@[stacks 040C "Picard group of a monoidal category"]
def PicardGroup : Type u :=
  Additive (Skeleton C)ˣ

/-- Tensor product gives the Picard group its additive group structure. -/
noncomputable instance : AddGroup (PicardGroup C) :=
  Additive.addGroup

/-- In a braided monoidal category, tensor product makes the Picard group commutative. -/
noncomputable instance [BraidedCategory C] : AddCommGroup (PicardGroup C) :=
  Additive.addCommGroup

namespace PicardGroup

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The skeleton class of an invertible object multiplied by its chosen inverse is the unit. -/
theorem toSkeleton_tensor_inverse (X : C) [isInvertibleObject X] :
    toSkeleton X * toSkeleton (isInvertibleObject.inverse X) = 1 := sorry

/-- The skeleton class of the chosen inverse multiplied by the original object is the unit. -/
theorem toSkeleton_inverse_tensor (X : C) [isInvertibleObject X] :
    toSkeleton (isInvertibleObject.inverse X) * toSkeleton X = 1 := sorry

/-- The Picard class represented by an invertible object. -/
@[stacks 040C "class of an invertible object"]
protected noncomputable def mk (X : C) [isInvertibleObject X] : PicardGroup C :=
  Additive.ofMul <|
    Units.mk (toSkeleton X) (toSkeleton (isInvertibleObject.inverse X))
      (toSkeleton_tensor_inverse X) (toSkeleton_inverse_tensor X)

/-- The chosen object representing a Picard class. -/
@[stacks 040C "chosen representative"]
protected noncomputable def repr (x : PicardGroup C) : C :=
  (fromSkeleton C).obj (Additive.toMul x).val

/-- The chosen representative of a Picard class is tensor-invertible. -/
instance reprIsInvertible (x : PicardGroup C) :
    isInvertibleObject (PicardGroup.repr x) := by
  apply (isInvertibleObject.iff_exists_tensorInverse (PicardGroup.repr x)).2
  let s : Skeleton C := (Additive.toMul x).val
  let t : Skeleton C := (Additive.toMul x).inv
  have hst : s * t = 1 := (Additive.toMul x).val_inv
  have hts : t * s = 1 := (Additive.toMul x).inv_val
  have hs : s = CategoryTheory.toSkeleton s.out := by
    simpa [CategoryTheory.toSkeleton] using Quotient.out_eq s
  have ht : t = CategoryTheory.toSkeleton t.out := by
    simpa [CategoryTheory.toSkeleton] using Quotient.out_eq t
  have hst' : CategoryTheory.toSkeleton (s.out ⊗ t.out) =
      CategoryTheory.toSkeleton (𝟙_ C) := by
    rw [← CategoryTheory.Skeleton.mul_eq s t, hst, CategoryTheory.Skeleton.one_eq]
  have hts' : CategoryTheory.toSkeleton (t.out ⊗ s.out) =
      CategoryTheory.toSkeleton (𝟙_ C) := by
    rw [← CategoryTheory.Skeleton.mul_eq t s, hts, CategoryTheory.Skeleton.one_eq]
  let hsIso : (CategoryTheory.fromSkeleton C).obj s ≅ s.out :=
    eqToIso (congrArg (CategoryTheory.fromSkeleton C).obj hs) ≪≫
      CategoryTheory.fromSkeletonToSkeletonIso s.out
  let htIso : (CategoryTheory.fromSkeleton C).obj t ≅ t.out :=
    eqToIso (congrArg (CategoryTheory.fromSkeleton C).obj ht) ≪≫
      CategoryTheory.fromSkeletonToSkeletonIso t.out
  refine ⟨(CategoryTheory.fromSkeleton C).obj t, ?_, ?_⟩
  · refine ⟨(hsIso ⊗ᵢ htIso) ≪≫
      (CategoryTheory.fromSkeletonToSkeletonIso (s.out ⊗ t.out)).symm ≪≫
      eqToIso (congrArg (CategoryTheory.fromSkeleton C).obj hst') ≪≫
      CategoryTheory.fromSkeletonToSkeletonIso (𝟙_ C)⟩
  · refine ⟨(htIso ⊗ᵢ hsIso) ≪≫
      (CategoryTheory.fromSkeletonToSkeletonIso (t.out ⊗ s.out)).symm ≪≫
      eqToIso (congrArg (CategoryTheory.fromSkeleton C).obj hts') ≪≫
      CategoryTheory.fromSkeletonToSkeletonIso (𝟙_ C)⟩

/-- The canonical skeleton comparison from the chosen representative of an invertible object's
Picard class to that object. -/
@[stacks 040C "representative of a class"]
noncomputable def reprMkIso (X : C) [isInvertibleObject X] :
    PicardGroup.repr (PicardGroup.mk X) ≅ X :=
  fromSkeletonToSkeletonIso X

/-- Taking the class of a chosen representative recovers the original Picard class. -/
theorem mk_repr (x : PicardGroup C) :
    PicardGroup.mk (PicardGroup.repr x) = x := sorry

/-- Picard classes are equal exactly when their chosen representatives are isomorphic. -/
theorem eq_iff_repr_iso {x y : PicardGroup C} :
    x = y ↔ Nonempty (PicardGroup.repr x ≅ PicardGroup.repr y) := sorry

/-- Two invertible objects determine the same Picard class exactly when they are isomorphic. -/
theorem mk_eq_mk_iff (X Y : C) [isInvertibleObject X] [isInvertibleObject Y] :
    PicardGroup.mk X = PicardGroup.mk Y ↔ Nonempty (X ≅ Y) := sorry

/-- The monoidal unit represents the zero Picard class. -/
theorem mk_unit :
    PicardGroup.mk (𝟙_ C) = (0 : PicardGroup C) := sorry

/-- An invertible object has zero Picard class exactly when it is isomorphic to the monoidal
unit. -/
theorem mk_eq_zero_iff (X : C) [isInvertibleObject X] :
    PicardGroup.mk X = (0 : PicardGroup C) ↔ Nonempty (X ≅ 𝟙_ C) := sorry

/-- Addition of Picard classes is represented by tensor product. -/
theorem mk_tensor (X Y : C) [isInvertibleObject X] [isInvertibleObject Y] :
    PicardGroup.mk (X ⊗ Y) = PicardGroup.mk X + PicardGroup.mk Y := sorry

/-- Negation of a Picard class is represented by the chosen tensor inverse. -/
theorem mk_inverse (X : C) [isInvertibleObject X] :
    PicardGroup.mk (isInvertibleObject.inverse X) = -PicardGroup.mk X := sorry

/-- The canonical skeleton comparison from the chosen representative of zero to the monoidal
unit. -/
@[stacks 040C "representative of zero"]
noncomputable def reprZeroIso :
    PicardGroup.repr (0 : PicardGroup C) ≅ 𝟙_ C :=
  fromSkeletonToSkeletonIso (𝟙_ C)

/-- The monoidal comparison identifying the chosen representative of a sum with the tensor
product of the chosen representatives. -/
@[stacks 040C "representative of a sum"]
noncomputable def reprAddIso (x y : PicardGroup C) :
    PicardGroup.repr (x + y) ≅ PicardGroup.repr x ⊗ PicardGroup.repr y :=
  (Functor.Monoidal.μIso (skeletonEquivalence C).functor (Additive.toMul x).val
    (Additive.toMul y).val).symm

/-- The chosen representative of a negative is isomorphic to the chosen tensor inverse. -/
@[stacks 040C "representative of a negative"]
noncomputable def reprNegIso (x : PicardGroup C) :
    PicardGroup.repr (-x) ≅
      isInvertibleObject.inverse (PicardGroup.repr x) :=
  isInvertibleObject.inverseIso (PicardGroup.repr x) <|
    ExactPairing.ofTensorInverse
      ((reprAddIso x (-x)).symm ≪≫
        eqToIso (congrArg PicardGroup.repr (add_neg_cancel x)) ≪≫ reprZeroIso)
      ((reprAddIso (-x) x).symm ≪≫
        eqToIso (congrArg PicardGroup.repr (neg_add_cancel x)) ≪≫ reprZeroIso)

section Functoriality

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- A monoidal functor induces an additive homomorphism of Picard groups. -/
@[stacks 040C "Picard map of a monoidal functor"]
noncomputable def map (F : C ⥤ D) [F.Monoidal] :
    PicardGroup C →+ PicardGroup D :=
  (Units.map (Skeleton.monoidHom F)).toAdditive

/-- The Picard map sends the class of an invertible object to the class of its image. -/
@[stacks 040C "functoriality on representatives", simp]
theorem map_mk (F : C ⥤ D) [F.Monoidal] (X : C) [isInvertibleObject X] :
    map F (PicardGroup.mk X) = PicardGroup.mk (F.obj X) := sorry

/-- Naturally isomorphic monoidal functors induce the same homomorphism on Picard groups. -/
@[stacks 040C "invariance under natural isomorphism"]
theorem map_congr {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (e : F ≅ G) :
    map F = map G := sorry

/-- Naturally isomorphic monoidal functors act identically on every Picard class. -/
theorem map_congr_apply {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]
    (e : F ≅ G) (x : PicardGroup C) :
    map F x = map G x := sorry

/-- A monoidal equivalence induces an additive equivalence of Picard groups. -/
@[stacks 040C "Picard equivalence of a monoidal equivalence"]
noncomputable def equiv (e : C ≌ D) [e.functor.Monoidal] :
    PicardGroup C ≃+ PicardGroup D :=
  (Units.mapEquiv (Skeleton.mulEquiv e)).toAdditive

/-- The additive homomorphism underlying the Picard equivalence is the Picard map of its
forward monoidal functor. -/
theorem equiv_toAddMonoidHom (e : C ≌ D) [e.functor.Monoidal] :
    (equiv e).toAddMonoidHom = map e.functor := sorry

/-- A Picard equivalence acts by the Picard map of its forward monoidal functor. -/
@[simp]
theorem equiv_apply (e : C ≌ D) [e.functor.Monoidal] (x : PicardGroup C) :
    equiv e x = map e.functor x := sorry

/-- The canonical skeleton comparison identifying the representative of a mapped Picard class
with the image of its representative. -/
@[stacks 040C "representative under a monoidal functor"]
noncomputable def reprMapIso (F : C ⥤ D) [F.Monoidal] (x : PicardGroup C) :
    PicardGroup.repr (map F x) ≅ F.obj (PicardGroup.repr x) :=
  fromSkeletonToSkeletonIso (F.obj (PicardGroup.repr x))

/-- The identity monoidal functor induces the identity on the Picard group. -/
@[simp]
theorem map_id :
    map (𝟭 C) = AddMonoidHom.id (PicardGroup C) := sorry

/-- Mapping a Picard class along the identity monoidal functor fixes it. -/
@[simp]
theorem map_id_apply (x : PicardGroup C) :
    map (𝟭 C) x = x := sorry

variable {E : Type u''} [Category.{v''} E] [MonoidalCategory E]

/-- Picard maps respect composition of monoidal functors. -/
@[simp]
theorem map_comp (F : C ⥤ D) (G : D ⥤ E) [F.Monoidal] [G.Monoidal] :
    map (F ⋙ G) = (map G).comp (map F) := sorry

/-- Mapping a Picard class along a composite is the composite of the induced Picard maps. -/
@[simp]
theorem map_comp_apply (F : C ⥤ D) (G : D ⥤ E) [F.Monoidal] [G.Monoidal]
    (x : PicardGroup C) :
    map (F ⋙ G) x = map G (map F x) := sorry

end Functoriality

end PicardGroup

end CategoryTheory.MonoidalCategory
