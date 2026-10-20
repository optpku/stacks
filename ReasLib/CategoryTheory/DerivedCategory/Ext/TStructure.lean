module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.CategoryTheory.Triangulated.TStructure.ShiftedHom
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Shifted Morphisms Across Derived T-Structure Bounds

The generic t-structure orthogonality theorem gives vanishing below the gap
between two bounds. At the boundary, the canonical homology map identifies a
shifted morphism with a morphism between the two extremal homology objects.
-/

noncomputable section

universe w v u

open CategoryTheory
open CategoryTheory.Pretriangulated

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A]

namespace DerivedCategory.ShiftedHom

namespace Boundary

/-- The canonical map from a boundary-degree shifted morphism to the induced
morphism between extremal homology objects. -/
@[stacks 06XS]
noncomputable def toHomology (X Y : DerivedCategory A) (a b : ℤ) :
    CategoryTheory.ShiftedHom X Y (b - a) →
      ((homologyFunctor A a).obj X ⟶ (homologyFunctor A b).obj Y) :=
  fun f ↦ (homologyFunctor A 0).shiftMap f a b (sub_add_cancel b a)

/-- The boundary-degree homology comparison is natural under
precomposition in its first argument. -/
@[simp, reassoc, stacks 06XS]
theorem toHomology_precomp {X' X Y : DerivedCategory A}
    (a b : ℤ) (f : X' ⟶ X)
    (g : CategoryTheory.ShiftedHom X Y (b - a)) :
    toHomology X' Y a b (f ≫ g) =
      (homologyFunctor A a).map f ≫ toHomology X Y a b g := sorry

/-- The boundary-degree homology comparison is natural under
postcomposition in its second argument. -/
@[simp, reassoc, stacks 06XS]
theorem toHomology_postcomp {X Y Y' : DerivedCategory A}
    (a b : ℤ) (f : CategoryTheory.ShiftedHom X Y (b - a)) (g : Y ⟶ Y') :
    toHomology X Y' a b (f ≫ g⟦b - a⟧') =
      toHomology X Y a b f ≫ (homologyFunctor A b).map g := sorry

/-- The top-degree quotient of the upper truncation uses the actual cycles and homology
quotient of the original cochain complex. -/
noncomputable def cochainProjection (K : CochainComplex A ℤ) (a : ℤ) :
    K.truncLE a ⟶ (CochainComplex.singleFunctor A a).obj (K.homology a) :=
  HomologicalComplex.mkHomToSingle
    ((K.truncLEXIsoCycles a).hom ≫ K.homologyπ a) (by sorry)

/-- The lowest-degree inclusion into the lower truncation uses the actual homology
subobject of the original cochain complex's opcycles. -/
noncomputable def cochainInclusion (K : CochainComplex A ℤ) (b : ℤ) :
    (CochainComplex.singleFunctor A b).obj (K.homology b) ⟶ K.truncGE b :=
  HomologicalComplex.mkHomFromSingle
    (K.homologyι b ≫ (K.truncGEXIsoOpcycles b).inv) (by sorry)

/-- The native representative of an object with an upper bound has that cohomology bound. -/
theorem representative_isLE (X : DerivedCategory A) (a : ℤ) (hX : X.IsLE a) :
    (Q.objPreimage X).IsLE a := by
  letI := hX
  letI : (Q.obj (Q.objPreimage X)).IsLE a :=
    TStructure.t.isLE_of_iso (Q.objObjPreimageIso X).symm a
  exact (isLE_Q_obj_iff _ _).mp inferInstance

/-- The native representative of an object with a lower bound has that cohomology bound. -/
theorem representative_isGE (Y : DerivedCategory A) (b : ℤ) (hY : Y.IsGE b) :
    (Q.objPreimage Y).IsGE b := by
  letI := hY
  letI : (Q.obj (Q.objPreimage Y)).IsGE b :=
    TStructure.t.isGE_of_iso (Q.objObjPreimageIso Y).symm b
  exact (isGE_Q_obj_iff _ _).mp inferInstance

/-- Homology of the given derived object identified with homology of its native
localization representative. Both maps are the existing realization comparisons. -/
noncomputable def representativeHomologyIso (X : DerivedCategory A) (a : ℤ) :
    (homologyFunctor A a).obj X ≅ (Q.objPreimage X).homology a :=
  (homologyFunctor A a).mapIso (Q.objObjPreimageIso X).symm ≪≫
    (homologyFunctorFactors A a).app (Q.objPreimage X)

/-- Formal localization of the native upper-truncation quasi-isomorphism. Its certificate
is Mathlib's proved truncation criterion applied to the supplied upper bound. -/
noncomputable def upperTruncationIso (X : DerivedCategory A) (a : ℤ) (hX : X.IsLE a) :
    Q.obj ((Q.objPreimage X).truncLE a) ≅ Q.obj (Q.objPreimage X) := by
  letI := representative_isLE X a hX
  exact asIso (Q.map ((Q.objPreimage X).ιTruncLE a))

/-- Formal localization of the native lower-truncation quasi-isomorphism, using only
Mathlib's proved criterion and the supplied lower bound. -/
noncomputable def lowerTruncationIso (Y : DerivedCategory A) (b : ℤ) (hY : Y.IsGE b) :
    Q.obj (Q.objPreimage Y) ≅ Q.obj ((Q.objPreimage Y).truncGE b) := by
  letI := representative_isGE Y b hY
  exact asIso (Q.map ((Q.objPreimage Y).πTruncGE b))

/-- Project an upper-bounded derived object onto its top cohomology in the same degree.
The map is the actual cycle quotient of its upper-truncated representative. -/
noncomputable def upperProjection (X : DerivedCategory A) (a : ℤ) (hX : X.IsLE a) :
    X ⟶ (singleFunctor A a).obj ((homologyFunctor A a).obj X) :=
  (Q.objObjPreimageIso X).inv ≫ (upperTruncationIso X a hX).inv ≫
    Q.map (cochainProjection (Q.objPreimage X) a) ≫
    (singleFunctor A a).map (representativeHomologyIso X a).inv

/-- Include the lowest cohomology of a lower-bounded derived object.
The map is the actual homology subobject of its lower-truncated representative. -/
noncomputable def lowerInclusion (Y : DerivedCategory A) (b : ℤ) (hY : Y.IsGE b) :
    (singleFunctor A b).obj ((homologyFunctor A b).obj Y) ⟶ Y :=
  (singleFunctor A b).map (representativeHomologyIso Y b).hom ≫
    Q.map (cochainInclusion (Q.objPreimage Y) b) ≫
    (lowerTruncationIso Y b hY).inv ≫ (Q.objObjPreimageIso Y).hom

/-- The actual boundary inverse. Project to the highest source cohomology, apply the
specified cohomology morphism, shift its single realization to the target degree, and
include it as the target's lowest cohomology. -/
@[stacks 06XS]
noncomputable def fromHomology (X Y : DerivedCategory A) (a b : ℤ)
    (hX : X.IsLE a) (hY : Y.IsGE b)
    (f : (homologyFunctor A a).obj X ⟶ (homologyFunctor A b).obj Y) :
    CategoryTheory.ShiftedHom X Y (b - a) :=
  upperProjection X a hX ≫ (singleFunctor A a).map f ≫
    ((singleFunctors A).shiftIso (b - a) a b (sub_add_cancel b a)).inv.app
      ((homologyFunctor A b).obj Y) ≫
    (lowerInclusion Y b hY)⟦b - a⟧'

/-- The displayed inverse recovers the specified extremal cohomology morphism. -/
@[simp, stacks 06XS]
theorem toHomology_fromHomology (X Y : DerivedCategory A) (a b : ℤ)
    (hX : X.IsLE a) (hY : Y.IsGE b)
    (f : (homologyFunctor A a).obj X ⟶ (homologyFunctor A b).obj Y) :
    toHomology X Y a b (fromHomology X Y a b hX hY f) = f := sorry

/-- Projecting and including at the boundary recovers the original shifted morphism. -/
@[simp, stacks 06XS]
theorem fromHomology_toHomology (X Y : DerivedCategory A) (a b : ℤ)
    (hX : X.IsLE a) (hY : Y.IsGE b) (f : CategoryTheory.ShiftedHom X Y (b - a)) :
    fromHomology X Y a b hX hY (toHomology X Y a b f) = f := sorry

/-- The boundary comparison with its specified inverse from native truncation maps. -/
@[stacks 06XS]
noncomputable def toHomologyEquiv (X Y : DerivedCategory A) (a b : ℤ)
    (hX : X.IsLE a) (hY : Y.IsGE b) :
    CategoryTheory.ShiftedHom X Y (b - a) ≃
      ((homologyFunctor A a).obj X ⟶ (homologyFunctor A b).obj Y) where
  toFun := toHomology X Y a b
  invFun := fromHomology X Y a b hX hY
  left_inv := fromHomology_toHomology X Y a b hX hY
  right_inv := toHomology_fromHomology X Y a b hX hY

/-- Bijectivity follows from the two specified directions and their inverse laws. -/
@[stacks 06XS]
theorem toHomology_bijective (X Y : DerivedCategory A)
    (a b : ℤ) (hX : X.IsLE a) (hY : Y.IsGE b) :
    Function.Bijective (toHomology X Y a b) :=
  (toHomologyEquiv X Y a b hX hY).bijective

/-- The inverse equivalence evaluates to the explicit truncation construction. -/
@[simp, stacks 06XS]
theorem toHomologyEquiv_symm_apply (X Y : DerivedCategory A) (a b : ℤ)
    (hX : X.IsLE a) (hY : Y.IsGE b)
    (f : (homologyFunctor A a).obj X ⟶ (homologyFunctor A b).obj Y) :
    (toHomologyEquiv X Y a b hX hY).symm f = fromHomology X Y a b hX hY f := rfl

/-- The boundary comparison as an additive homomorphism.

The source and target are hom groups in Abelian categories, so the canonical boundary map is
additive.  Naming this map separately lets downstream code use additive APIs without unfolding
the ordinary function or constructing an anonymous `AddMonoidHom`. -/
@[stacks 06XS]
noncomputable def toHomologyAddHom (X Y : DerivedCategory A) (a b : ℤ) :
    CategoryTheory.ShiftedHom X Y (b - a) →+
      ((homologyFunctor A a).obj X ⟶ (homologyFunctor A b).obj Y) where
  toFun := toHomology X Y a b
  map_zero' := sorry
  map_add' := sorry

/-- Evaluation of the additive boundary homomorphism is the canonical comparison function. -/
@[simp, stacks 06XS]
theorem toHomologyAddHom_apply (X Y : DerivedCategory A) (a b : ℤ)
    (f : CategoryTheory.ShiftedHom X Y (b - a)) :
    toHomologyAddHom X Y a b f = toHomology X Y a b f := rfl

/-- The boundary comparison packaged as an additive equivalence. -/
@[stacks 06XS]
noncomputable def toHomologyAddEquiv (X Y : DerivedCategory A) (a b : ℤ)
    (hX : X.IsLE a) (hY : Y.IsGE b) :
    CategoryTheory.ShiftedHom X Y (b - a) ≃+
      ((homologyFunctor A a).obj X ⟶ (homologyFunctor A b).obj Y) :=
  { toHomologyEquiv X Y a b hX hY with
    map_add' := (toHomologyAddHom X Y a b).map_add }

/-- The additive equivalence retains the same explicit truncation inverse. -/
@[simp, stacks 06XS]
theorem toHomologyAddEquiv_symm_apply (X Y : DerivedCategory A) (a b : ℤ)
    (hX : X.IsLE a) (hY : Y.IsGE b)
    (f : (homologyFunctor A a).obj X ⟶ (homologyFunctor A b).obj Y) :
    (toHomologyAddEquiv X Y a b hX hY).symm f = fromHomology X Y a b hX hY f := rfl

/-- Evaluation of the additive boundary equivalence is the canonical comparison function. -/
@[simp, stacks 06XS]
theorem toHomologyAddEquiv_apply (X Y : DerivedCategory A) (a b : ℤ)
    (hX : X.IsLE a) (hY : Y.IsGE b)
    (f : CategoryTheory.ShiftedHom X Y (b - a)) :
    toHomologyAddEquiv X Y a b hX hY f = toHomology X Y a b f := rfl

/-- Evaluation of the packaged boundary equivalence is the canonical homology comparison. -/
@[simp, stacks 06XS]
theorem toHomologyEquiv_apply (X Y : DerivedCategory A) (a b : ℤ)
    (hX : X.IsLE a) (hY : Y.IsGE b)
    (f : CategoryTheory.ShiftedHom X Y (b - a)) :
    toHomologyEquiv X Y a b hX hY f = toHomology X Y a b f := rfl

/-- Naturality of the boundary equivalence in the derived source. -/
@[reassoc, stacks 06XS]
theorem toHomologyEquiv_naturality_left
    {X' X Y : DerivedCategory A} (a b : ℤ)
    (hX' : X'.IsLE a) (hX : X.IsLE a) (hY : Y.IsGE b)
    (f : X' ⟶ X) (g : CategoryTheory.ShiftedHom X Y (b - a)) :
    toHomologyEquiv X' Y a b hX' hY (f ≫ g) =
      (homologyFunctor A a).map f ≫ toHomologyEquiv X Y a b hX hY g := sorry

/-- Naturality of the boundary equivalence in the derived target. -/
@[reassoc, stacks 06XS]
theorem toHomologyEquiv_naturality_right
    {X Y Y' : DerivedCategory A} (a b : ℤ)
    (hX : X.IsLE a) (hY : Y.IsGE b) (hY' : Y'.IsGE b)
    (f : CategoryTheory.ShiftedHom X Y (b - a)) (g : Y ⟶ Y') :
    toHomologyEquiv X Y' a b hX hY' (f ≫ g⟦b - a⟧') =
      toHomologyEquiv X Y a b hX hY f ≫ (homologyFunctor A b).map g := sorry

/-- Naturality of the inverse boundary equivalence in the derived source.

This form transports a homology morphism back to a shifted morphism before precomposition,
which avoids making downstream users invert `toHomologyEquiv_naturality_left` by hand. -/
@[reassoc, stacks 06XS]
theorem toHomologyEquiv_naturality_left_symm
    {X' X Y : DerivedCategory A} (a b : ℤ)
    (hX' : X'.IsLE a) (hX : X.IsLE a) (hY : Y.IsGE b)
    (f : X' ⟶ X)
    (g : (homologyFunctor A a).obj X ⟶ (homologyFunctor A b).obj Y) :
    (toHomologyEquiv X' Y a b hX' hY).symm
        ((homologyFunctor A a).map f ≫ g) =
      f ≫ (toHomologyEquiv X Y a b hX hY).symm g := sorry

/-- Naturality of the inverse boundary equivalence in the derived target.

This form transports a homology morphism back to a shifted morphism after postcomposition,
which is the direct interface for target-side Ext transport. -/
@[reassoc, stacks 06XS]
theorem toHomologyEquiv_naturality_right_symm
    {X Y Y' : DerivedCategory A} (a b : ℤ)
    (hX : X.IsLE a) (hY : Y.IsGE b) (hY' : Y'.IsGE b)
    (f : (homologyFunctor A a).obj X ⟶ (homologyFunctor A b).obj Y)
    (g : Y ⟶ Y') :
    (toHomologyEquiv X Y' a b hX hY').symm
        (f ≫ (homologyFunctor A b).map g) =
      (toHomologyEquiv X Y a b hX hY).symm f ≫ g⟦b - a⟧' := sorry

end Boundary

/-- Derived-category specialization of t-structure orthogonality for shifted
morphisms below the gap between an upper and a lower bound. -/
@[stacks 06XS]
theorem subsingleton_of_lt_sub (X Y : DerivedCategory A)
    (a b n : ℤ) (hX : X.IsLE a) (hY : Y.IsGE b) (hn : n < b - a) :
    Subsingleton (CategoryTheory.ShiftedHom X Y n) := sorry

end DerivedCategory.ShiftedHom

namespace DerivedCategory.Single.ShiftedHom

/-- Negative shifted morphisms between single-degree derived objects form a
subsingleton. -/
@[stacks 06XS]
theorem subsingleton_of_neg (B A' : A) (i : ℤ) (hi : i < 0) :
    Subsingleton
      (CategoryTheory.ShiftedHom
        ((singleFunctor A 0).obj B) ((singleFunctor A 0).obj A') i) := sorry

/-- Shifted morphisms of degree zero between single-degree derived objects
are canonically equivalent to morphisms in the abelian category. -/
@[stacks 06XS]
noncomputable def zeroEquiv (B A' : A) :
    CategoryTheory.ShiftedHom
        ((singleFunctor A 0).obj B) ((singleFunctor A 0).obj A') (0 : ℤ) ≃ (B ⟶ A') :=
  (CategoryTheory.ShiftedHom.homEquiv
      (X := (singleFunctor A 0).obj B)
      (Y := (singleFunctor A 0).obj A') (0 : ℤ) rfl).symm |>.trans
    ((Functor.FullyFaithful.ofFullyFaithful (singleFunctor A 0)).homEquiv
      (X := B) (Y := A')).symm

/-- The inverse zero-degree equivalence sends an abelian morphism to its
single-functor image viewed as a shifted morphism. -/
@[simp]
theorem zeroEquiv_symm_apply (B A' : A) (f : B ⟶ A') :
    (zeroEquiv B A').symm f =
      CategoryTheory.ShiftedHom.mk₀
        (0 : ℤ) rfl ((singleFunctor A 0).map f) := sorry

/-- Applying the zero-degree equivalence to the shifted image of an abelian
morphism recovers that morphism. -/
@[simp]
theorem zeroEquiv_apply_mk₀ (B A' : A) (f : B ⟶ A') :
    zeroEquiv B A'
        (CategoryTheory.ShiftedHom.mk₀
          (0 : ℤ) rfl ((singleFunctor A 0).map f)) = f := sorry

end DerivedCategory.Single.ShiftedHom
