module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Basic

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealQuotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Coborder

/-!
# Conormal sheaves and total conormal algebras of immersions of algebraic spaces

The conormal sheaf of an immersion `i : Z ⟶ X` is `I / I²` for the coborder closed
immersion `Z ⟶ X \ ∂Z`, pulled back to `Z`. The total conormal algebra is the
associated graded `𝒪_Z`-algebra of that coborder ideal: the sectionwise associated
graded is sheafified on `X \ ∂Z`, pulled back along the coborder lift, and pushed
out along the inverse-image structure map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory Opposite AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Inverse image of commutative-ring sheaves along a morphism of algebraic spaces. -/
noncomputable abbrev commRingInverseImage {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology Y) CommRingCat.{u} ⥤
      Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  CategoryTheory.Sheaf.InternalCommRing.toInternal.{u + 1, u, u} ⋙ internalCommRingInverseImage f ⋙
    CategoryTheory.Sheaf.InternalCommRing.fromInternal.{u + 1, u, u}

/-- Commutative-ring inverse image retains the canonical internal-ring construction. -/
theorem commRingInverseImage_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commRingInverseImage f =
      CategoryTheory.Sheaf.InternalCommRing.toInternal.{u + 1, u, u} ⋙ internalCommRingInverseImage f ⋙
        CategoryTheory.Sheaf.InternalCommRing.fromInternal.{u + 1, u, u} :=
  rfl

/-- The inverse-image structure map `j^{-1} 𝒪_Y ⟶ 𝒪_X` adjunct to
`𝒪_Y ⟶ j_* 𝒪_X`. -/
noncomputable def inverseImageStructureSheafHom {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (commRingInverseImage f).obj (commStructureSheaf Y) ⟶
      commStructureSheaf X :=
  commInverseImageStructureSheafMap f

/-- The structure map is the actual geometric adjunction transpose on internal commutative rings. -/
theorem inverseImageStructureSheafHom_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    inverseImageStructureSheafHom f =
      commInverseImageStructureSheafMap f :=
  rfl

namespace ConormalAlgebra

variable {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/-- The kernel map `𝒪_{X \ ∂Z} ⟶ j_* 𝒪_Z` of the coborder closed immersion. -/
noncomputable def coborderKernelMap :
    commStructureSheaf (Hom.coborder i) ⟶
      (commRingPushforward (IsImmersion.liftCoborder i)).obj
        (commStructureSheaf Z) :=
  commStructureSheafMap (IsImmersion.liftCoborder i)

/-- `coborderKernelMap i` is the structure-sheaf map of the coborder lift. -/
theorem coborderKernelMap_eq :
    coborderKernelMap i =
      commStructureSheafMap (IsImmersion.liftCoborder i) :=
  rfl

/-- Restriction of sections carries the coborder kernel ideal into the next kernel
ideal. -/
theorem coborderKernel_sectionIdeal_le_comap
    {U V : (smallEtaleSite (Hom.coborder i))ᵒᵖ} (f : U ⟶ V) :
    KernelIdeal.sectionIdeal (coborderKernelMap i) U ≤
      Ideal.comap
        (((commStructureSheaf (Hom.coborder i)).obj.map f).hom)
        (KernelIdeal.sectionIdeal (coborderKernelMap i) V) := by
  intro x hx
  rw [Ideal.mem_comap, KernelIdeal.sectionIdeal, RingHom.mem_ker]
  have hnat := (InducedCategory.Hom.hom (coborderKernelMap i)).naturality f
  have hx' : ((InducedCategory.Hom.hom (coborderKernelMap i)).app U).hom x = 0 := by
    simpa [KernelIdeal.sectionIdeal, RingHom.mem_ker] using hx
  have hcomp :=
    congrArg
      (fun φ : (commStructureSheaf (Hom.coborder i)).obj.obj U ⟶
          ((commRingPushforward (IsImmersion.liftCoborder i)).obj
              (commStructureSheaf Z)).obj.obj V =>
        φ.hom x)
      hnat
  simpa [ConcreteCategory.comp_apply, hx', map_zero] using hcomp

/-- The sectionwise associated graded ring of the coborder kernel ideal. -/
noncomputable def coborderGradeObj (U : (smallEtaleSite (Hom.coborder i))ᵒᵖ) :
    CommRingCat.{u} :=
  CommRingCat.of
    (Ideal.AssociatedGraded.ring (KernelIdeal.sectionIdeal (coborderKernelMap i) U))

/-- Restriction of the sectionwise coborder associated graded rings. -/
noncomputable def coborderGradeMap
    {U V : (smallEtaleSite (Hom.coborder i))ᵒᵖ} (f : U ⟶ V) :
    coborderGradeObj i U ⟶ coborderGradeObj i V :=
  CommRingCat.ofHom
    (Ideal.AssociatedGraded.map
      (((commStructureSheaf (Hom.coborder i)).obj.map f).hom)
      (coborderKernel_sectionIdeal_le_comap i f))

/-- The coborder associated graded as a presheaf of commutative rings. -/
noncomputable def coborderGradePresheaf :
    (smallEtaleSite (Hom.coborder i))ᵒᵖ ⥤ CommRingCat.{u} where
  obj := coborderGradeObj i
  map := coborderGradeMap i
  map_id := sorry
  map_comp := sorry

/-- Evaluating the coborder associated graded presheaf recovers the sectionwise
associated graded ring. -/
theorem coborderGradePresheaf_obj (U : (smallEtaleSite (Hom.coborder i))ᵒᵖ) :
    (coborderGradePresheaf i).obj U = coborderGradeObj i U :=
  rfl

/-- The coborder associated graded, as the sheafification of the sectionwise
associated graded of the coborder kernel ideal. -/
noncomputable def coborderGradeSheaf :
    Sheaf (smallEtaleTopology (Hom.coborder i)) CommRingCat.{u} :=
  (presheafToSheaf (smallEtaleTopology (Hom.coborder i)) CommRingCat.{u}).obj
    (coborderGradePresheaf i)

/-- `coborderGradeSheaf i` is the sheafification of `coborderGradePresheaf i`. -/
theorem coborderGradeSheaf_eq :
    coborderGradeSheaf i =
      (presheafToSheaf (smallEtaleTopology (Hom.coborder i)) CommRingCat.{u}).obj
        (coborderGradePresheaf i) :=
  rfl

/-- The component at `U` of the coborder associated graded structure map. -/
noncomputable def coborderStructureMap_app
    (U : (smallEtaleSite (Hom.coborder i))ᵒᵖ) :
    (commStructureSheaf (Hom.coborder i)).obj.obj U ⟶ coborderGradeObj i U :=
  CommRingCat.ofHom
    (algebraMap
      ((commStructureSheaf (Hom.coborder i)).obj.obj U)
      (Ideal.AssociatedGraded.ring
        (KernelIdeal.sectionIdeal (coborderKernelMap i) U)))

/-- The structure map from `𝒪_{X \ ∂Z}` to the coborder associated graded, as a
morphism of presheaves. -/
noncomputable def coborderStructureMapPresheaf :
    (commStructureSheaf (Hom.coborder i)).obj ⟶ coborderGradePresheaf i where
  app U := coborderStructureMap_app i U
  naturality := fun _ _ _ => sorry

/-- The component of `coborderStructureMapPresheaf i` at `U` is the associated
graded algebra map. -/
theorem coborderStructureMapPresheaf_app
    (U : (smallEtaleSite (Hom.coborder i))ᵒᵖ) :
    (coborderStructureMapPresheaf i).app U = coborderStructureMap_app i U :=
  rfl

/-- The structure map from `𝒪_{X \ ∂Z}` to the sheafified coborder associated
graded. -/
noncomputable def coborderStructureMap :
    commStructureSheaf (Hom.coborder i) ⟶ coborderGradeSheaf i :=
  CategoryTheory.Sheaf.homEquiv.symm
    (coborderStructureMapPresheaf i ≫
      toSheafify (smallEtaleTopology (Hom.coborder i)) (coborderGradePresheaf i))

/-- The coborder associated graded structure map is the sheafification of the
sectionwise algebra maps. -/
theorem coborderStructureMap_eq :
    coborderStructureMap i =
      CategoryTheory.Sheaf.homEquiv.symm
        (coborderStructureMapPresheaf i ≫
          toSheafify (smallEtaleTopology (Hom.coborder i))
            (coborderGradePresheaf i)) :=
  rfl

/-- The coborder associated graded as a quasi-coherent algebra on `X \ ∂Z`. -/
noncomputable def coborderTotal : (Hom.coborder i).QcAlgebraUnder where
  obj := Under.mk (coborderStructureMap i)
  property := sorry

/-- The underlying algebra object of `coborderTotal i` is `Under.mk` of the coborder
structure map. -/
theorem coborderTotal_obj :
    (coborderTotal i).obj = Under.mk (coborderStructureMap i) :=
  rfl

/-- The total conormal algebra sheaf of an immersion, as the pushout of
`j^{-1} 𝒪_{X \ ∂Z} ⟶ 𝒪_Z` against the inverse image of the coborder associated
graded. -/
noncomputable def totalSheaf :
    Sheaf (smallEtaleTopology Z) CommRingCat.{u} :=
  pushout
    (inverseImageStructureSheafHom (IsImmersion.liftCoborder i))
    ((commRingInverseImage (IsImmersion.liftCoborder i)).map
      (coborderStructureMap i))

/-- The total conormal algebra sheaf is the indicated pushout of inverse-image
structure and coborder associated graded data. -/
theorem totalSheaf_eq :
    totalSheaf i =
      pushout
        (inverseImageStructureSheafHom (IsImmersion.liftCoborder i))
        ((commRingInverseImage (IsImmersion.liftCoborder i)).map
          (coborderStructureMap i)) :=
  rfl

/-- The structure map making the total conormal algebra an `𝒪_Z`-algebra. -/
noncomputable def structureMap :
    commStructureSheaf Z ⟶ totalSheaf i :=
  pushout.inl
    (inverseImageStructureSheafHom (IsImmersion.liftCoborder i))
    ((commRingInverseImage (IsImmersion.liftCoborder i)).map
      (coborderStructureMap i))

/-- The structure map of the total conormal algebra is the first pushout inclusion. -/
theorem structureMap_eq :
    structureMap i =
      pushout.inl
        (inverseImageStructureSheafHom (IsImmersion.liftCoborder i))
        ((commRingInverseImage (IsImmersion.liftCoborder i)).map
          (coborderStructureMap i)) :=
  rfl

/-- The total conormal algebra `C_{Z/X,*}` of an immersion, as a quasi-coherent
`𝒪_Z`-algebra. -/
noncomputable def total : Z.QcAlgebraUnder where
  obj := Under.mk (structureMap i)
  property := sorry

/-- The underlying `𝒪_Z`-algebra of `total i` is `Under.mk` of its structure map. -/
theorem total_obj : (total i).obj = Under.mk (structureMap i) :=
  rfl

/-- The right-hand sheaf of the total conormal algebra is `totalSheaf i`. -/
theorem total_sheaf : (total i).obj.right = totalSheaf i :=
  rfl

/-- The total conormal algebra is the `𝒪_Z`-algebra associated to the coborder
associated graded of the kernel of `𝒪_{X \ ∂Z} ⟶ j_* 𝒪_Z`. -/
theorem total_spec :
    (total i).obj = Under.mk (structureMap i) ∧
      totalSheaf i =
        pushout
          (inverseImageStructureSheafHom (IsImmersion.liftCoborder i))
          ((commRingInverseImage (IsImmersion.liftCoborder i)).map
            (coborderStructureMap i)) ∧
      IsClosedImmersion (IsImmersion.liftCoborder i) :=
  sorry

/-- Pushforward of the degree-one conormal piece along the coborder closed immersion
is isomorphic to the successive coborder quotient `I / I²`. -/
theorem grade_pushforward_one :
    Nonempty
      ((Modules.pushforward (IsImmersion.liftCoborder i)).obj (Hom.conormalSheaf i) ≅
        Modules.quotientByIdeal
          (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
          (Hom.idealSheaf (IsImmersion.liftCoborder i))) :=
  sorry

/-- The degree-`n` homogeneous component of the sectionwise coborder associated
graded at `U`. -/
noncomputable abbrev coborderGradeSection (n : ℕ)
    (U : (smallEtaleSite (Hom.coborder i))ᵒᵖ) :=
  Ideal.AssociatedGraded.grade (KernelIdeal.sectionIdeal (coborderKernelMap i) U) n

/-- `coborderGradeSection i n U` is the successive quotient of coborder kernel
powers in degree `n`. -/
theorem coborderGradeSection_eq (n : ℕ)
    (U : (smallEtaleSite (Hom.coborder i))ᵒᵖ) :
    coborderGradeSection i n U =
      Ideal.AssociatedGraded.grade (KernelIdeal.sectionIdeal (coborderKernelMap i) U) n :=
  rfl

/-- Degree one of the sectionwise coborder associated graded is the successive
quotient whose sheafification pulls back to the conormal sheaf. -/
theorem coborderGradeSection_one (U : (smallEtaleSite (Hom.coborder i))ᵒᵖ) :
    coborderGradeSection i 1 U =
      Ideal.AssociatedGraded.grade (KernelIdeal.sectionIdeal (coborderKernelMap i) U) 1 :=
  rfl

/-- The coborder associated graded as an `𝒪_{X \ ∂Z}`-module, by restriction of scalars
along its structure map. -/
noncomputable def coborderGradeAsModule :=
  (restrictionAlong (coborderStructureMap i)).obj
    (unitModule (smallEtaleTopology (Hom.coborder i)) (coborderGradeSheaf i))

/-- `coborderGradeAsModule i` is restriction of scalars of the unit module of the coborder
associated graded. -/
theorem coborderGradeAsModule_eq :
    coborderGradeAsModule i =
      (restrictionAlong (coborderStructureMap i)).obj
        (unitModule (smallEtaleTopology (Hom.coborder i)) (coborderGradeSheaf i)) :=
  rfl

/-- The right-hand pushout inclusion of the coborder associated graded into the total
conormal algebra sheaf. -/
noncomputable def totalInr :
    (commRingInverseImage (IsImmersion.liftCoborder i)).obj (coborderGradeSheaf i) ⟶
      totalSheaf i :=
  pushout.inr
    (inverseImageStructureSheafHom (IsImmersion.liftCoborder i))
    ((commRingInverseImage (IsImmersion.liftCoborder i)).map (coborderStructureMap i))

/-- `totalInr i` is the second pushout inclusion into `totalSheaf i`. -/
theorem totalInr_eq :
    totalInr i =
      pushout.inr
        (inverseImageStructureSheafHom (IsImmersion.liftCoborder i))
        ((commRingInverseImage (IsImmersion.liftCoborder i)).map
          (coborderStructureMap i)) :=
  rfl

end ConormalAlgebra

end AlgebraicGeometry.AlgebraicSpace
