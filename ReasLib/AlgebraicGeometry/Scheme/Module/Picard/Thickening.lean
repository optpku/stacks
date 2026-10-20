module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Picard.SquareZero
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.SquareZeroExtension

/-!
# Picard groups of first-order thickenings

This file transports the square-zero Picard cohomology sequence from the
inverse-image presentation of a first-order thickening to the ambient scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Sheaf
open SheafOfModules
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.KernelIdeal

noncomputable section

universe u

namespace AlgebraicGeometry.IsFirstOrderThickening

variable {X X' : Scheme.{u}} (i : X ⟶ X') [IsFirstOrderThickening i]

/-- The forward map from global sections of the inverse-image presentation to
global sections of the ambient thickening. -/
noncomputable def presentationGlobalSectionsHom :
    (presentationSheaf i).1.obj (op ⊤) ⟶ X'.sheaf.1.obj (op ⊤) :=
  let h := i.isClosedEmbedding.toHomeomorphOfSurjective i.surjective
  let hfunctor := h.isOpenMap.functor
  let htop : hfunctor.obj (⊤ : X.Opens) = ⊤ :=
    Opens.ext (Set.image_univ_of_surjective i.surjective)
  ((h.isOpenEmbedding.sheafPullbackIso CommRingCat.{u}).app
      X'.sheaf).hom.hom.app (op ⊤) ≫
    eqToHom (congrArg (fun U : X'.Opens ↦ X'.sheaf.1.obj (op U)) htop)

/-- The inverse map from ambient global sections to global sections of the
inverse-image presentation. -/
noncomputable def presentationGlobalSectionsInv :
    X'.sheaf.1.obj (op ⊤) ⟶ (presentationSheaf i).1.obj (op ⊤) :=
  let h := i.isClosedEmbedding.toHomeomorphOfSurjective i.surjective
  let hfunctor := h.isOpenMap.functor
  let htop : hfunctor.obj (⊤ : X.Opens) = ⊤ :=
    Opens.ext (Set.image_univ_of_surjective i.surjective)
  eqToHom (congrArg
      (fun U : X'.Opens ↦ X'.sheaf.1.obj (op U)) htop).symm ≫
    ((h.isOpenEmbedding.sheafPullbackIso CommRingCat.{u}).app
      X'.sheaf).inv.hom.app (op ⊤)

/-- The global-sections comparison followed by its inverse is the identity. -/
theorem presentationGlobalSections_hom_inv_id :
    presentationGlobalSectionsHom i ≫ presentationGlobalSectionsInv i = 𝟙 _ := sorry

/-- The inverse global-sections comparison followed by the forward comparison
is the identity. -/
theorem presentationGlobalSections_inv_hom_id :
    presentationGlobalSectionsInv i ≫ presentationGlobalSectionsHom i = 𝟙 _ := sorry

/-- The canonical comparison between global ring sections of the inverse-image
presentation and global ring sections of the ambient thickening. -/
noncomputable def presentationGlobalSectionsIso :
    (presentationSheaf i).1.obj (op ⊤) ≅ X'.sheaf.1.obj (op ⊤) where
  hom := presentationGlobalSectionsHom i
  inv := presentationGlobalSectionsInv i
  hom_inv_id := presentationGlobalSections_hom_inv_id i
  inv_hom_id := presentationGlobalSections_inv_hom_id i

/-- The sectionwise map from ambient units to units of the inverse-image
presentation. -/
noncomputable def presentationUnitsSectionMapFunction :
    (Sheaf.unitsAddSheaf X'.sheaf).1.obj (op ⊤) →
      (Sheaf.unitsAddSheaf (presentationSheaf i)).1.obj (op ⊤) :=
  fun g ↦ Sheaf.unitsAddSheafSection (presentationSheaf i)
    (Units.map (presentationGlobalSectionsIso i).inv.hom.toMonoidHom
      (Sheaf.unitsAddSheafUnit X'.sheaf g))

/-- The ambient-to-presentation map on units sections preserves zero. -/
theorem presentationUnitsSectionMapFunction_zero :
    presentationUnitsSectionMapFunction i 0 = 0 := sorry

/-- The ambient-to-presentation map on units sections preserves addition. -/
theorem presentationUnitsSectionMapFunction_add
    (x y : (Sheaf.unitsAddSheaf X'.sheaf).1.obj (op ⊤)) :
    presentationUnitsSectionMapFunction i (x + y) =
      presentationUnitsSectionMapFunction i x +
        presentationUnitsSectionMapFunction i y := sorry

/-- The additive map from ambient global units to global units of the
inverse-image presentation. -/
noncomputable def presentationUnitsSectionMap :
    (Sheaf.unitsAddSheaf X'.sheaf).1.obj (op ⊤) →+
      (Sheaf.unitsAddSheaf (presentationSheaf i)).1.obj (op ⊤) where
  toFun := presentationUnitsSectionMapFunction i
  map_zero' := presentationUnitsSectionMapFunction_zero i
  map_add' := presentationUnitsSectionMapFunction_add i

/-- The sectionwise inverse map from units of the inverse-image presentation
to ambient units. -/
noncomputable def presentationUnitsSectionInvFunction :
    (Sheaf.unitsAddSheaf (presentationSheaf i)).1.obj (op ⊤) →
      (Sheaf.unitsAddSheaf X'.sheaf).1.obj (op ⊤) :=
  fun g ↦ Sheaf.unitsAddSheafSection X'.sheaf
    (Units.map (presentationGlobalSectionsIso i).hom.hom.toMonoidHom
      (Sheaf.unitsAddSheafUnit (presentationSheaf i) g))

/-- The presentation-to-ambient map on units sections preserves zero. -/
theorem presentationUnitsSectionInvFunction_zero :
    presentationUnitsSectionInvFunction i 0 = 0 := sorry

/-- The presentation-to-ambient map on units sections preserves addition. -/
theorem presentationUnitsSectionInvFunction_add
    (x y : (Sheaf.unitsAddSheaf (presentationSheaf i)).1.obj (op ⊤)) :
    presentationUnitsSectionInvFunction i (x + y) =
      presentationUnitsSectionInvFunction i x +
        presentationUnitsSectionInvFunction i y := sorry

/-- The additive map from presentation global units to ambient global units. -/
noncomputable def presentationUnitsSectionInv :
    (Sheaf.unitsAddSheaf (presentationSheaf i)).1.obj (op ⊤) →+
      (Sheaf.unitsAddSheaf X'.sheaf).1.obj (op ⊤) where
  toFun := presentationUnitsSectionInvFunction i
  map_zero' := presentationUnitsSectionInvFunction_zero i
  map_add' := presentationUnitsSectionInvFunction_add i

/-- The ambient-to-presentation units map is left inverse to its comparison. -/
theorem presentationUnitsSectionMap_leftInverse
    (x : (Sheaf.unitsAddSheaf X'.sheaf).1.obj (op ⊤)) :
    presentationUnitsSectionInv i (presentationUnitsSectionMap i x) = x := sorry

/-- The ambient-to-presentation units map is right inverse to its comparison. -/
theorem presentationUnitsSectionMap_rightInverse
    (x : (Sheaf.unitsAddSheaf (presentationSheaf i)).1.obj (op ⊤)) :
    presentationUnitsSectionMap i (presentationUnitsSectionInv i x) = x := sorry

/-- The canonical additive equivalence between ambient global units and the
global units of the inverse-image presentation. -/
noncomputable def presentationUnitsSectionsEquiv :
    (Sheaf.unitsAddSheaf X'.sheaf).1.obj (op ⊤) ≃+
      (Sheaf.unitsAddSheaf (presentationSheaf i)).1.obj (op ⊤) where
  toFun := presentationUnitsSectionMap i
  invFun := presentationUnitsSectionInv i
  left_inv := presentationUnitsSectionMap_leftInverse i
  right_inv := presentationUnitsSectionMap_rightInverse i
  map_add' := (presentationUnitsSectionMap i).map_add

/-- The canonical pullback comparison from the Picard group of the ambient
scheme to that of its inverse-image presentation. -/
noncomputable def presentationPicardMap :
    X'.PicardGroup →+
      SheafOfModules.RingedSite.PicardGroup
        (Opens.grothendieckTopology X.toTopCat) (presentationSheaf i) :=
  Scheme.Hom.picardPullback (reconstructionHom i)

/-- The underlying inverse function to the Picard comparison. -/
noncomputable def presentationPicardInverseFunction :
    SheafOfModules.RingedSite.PicardGroup
        (Opens.grothendieckTopology X.toTopCat) (presentationSheaf i) →
      X'.PicardGroup :=
  Function.invFun (presentationPicardMap i)

/-- The inverse Picard comparison sends zero to zero. -/
theorem presentationPicardInverseFunction_zero :
    presentationPicardInverseFunction i 0 = 0 := sorry

/-- The inverse Picard comparison preserves addition. -/
theorem presentationPicardInverseFunction_add
    (x y : SheafOfModules.RingedSite.PicardGroup
      (Opens.grothendieckTopology X.toTopCat) (presentationSheaf i)) :
    presentationPicardInverseFunction i (x + y) =
      presentationPicardInverseFunction i x +
        presentationPicardInverseFunction i y := sorry

/-- Pullback to the presentation followed by its inverse recovers an ambient
Picard class. -/
theorem presentationPicardMap_leftInverse (x : X'.PicardGroup) :
    presentationPicardInverseFunction i (presentationPicardMap i x) = x := sorry

/-- The inverse comparison followed by pullback recovers a presentation
Picard class. -/
theorem presentationPicardMap_rightInverse
    (x : SheafOfModules.RingedSite.PicardGroup
      (Opens.grothendieckTopology X.toTopCat) (presentationSheaf i)) :
    presentationPicardMap i (presentationPicardInverseFunction i x) = x := sorry

/-- The canonical additive equivalence between the Picard group of the
ambient thickening and the Picard group of its inverse-image presentation. -/
noncomputable def presentationPicardEquiv :
    X'.PicardGroup ≃+
      SheafOfModules.RingedSite.PicardGroup
        (Opens.grothendieckTopology X.toTopCat) (presentationSheaf i) where
  toFun := presentationPicardMap i
  invFun := presentationPicardInverseFunction i
  left_inv := presentationPicardMap_leftInverse i
  right_inv := presentationPicardMap_rightInverse i
  map_add' := (presentationPicardMap i).map_add

variable [hWeakSheafify : HasWeakSheafify
  (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}]
variable [hLocallyBijective :
  (Opens.grothendieckTopology X.toTopCat).WEqualsLocallyBijective
  AddCommGrpCat.{u}]
variable [hExt : HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
variable [hExt' : HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X'.toTopCat) AddCommGrpCat.{u})]
variable [hSheafify : HasSheafify
  (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}]
variable [hSheafify' : HasSheafify
  (Opens.grothendieckTopology X'.toTopCat) AddCommGrpCat.{u}]
variable [hCommRingToRing :
  (Opens.grothendieckTopology X.toTopCat).HasSheafCompose
  (forget₂ CommRingCat.{u} RingCat.{u})]
variable [hRingToAddCommGrp :
  (Opens.grothendieckTopology X.toTopCat).HasSheafCompose
  (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [hForgetCommRing :
  (Opens.grothendieckTopology X.toTopCat).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [hTypeSheafify : HasWeakSheafify
  (Opens.grothendieckTopology X.toTopCat) (Type u)]
variable [hXLocallyRinged : Sheaf.IsLocallyRinged X.sheaf]

/-- The inverse-image presentation sheaf of a first-order thickening is
locally ringed. -/
instance presentationSheaf_isLocallyRinged :
    Sheaf.IsLocallyRinged (presentationSheaf i) := sorry

/-- The degree-zero units cohomology of the ambient thickening is canonically
identified with that of its inverse-image presentation on `X`. -/
noncomputable def presentationUnitsH0Equiv :
    (@Sheaf.H X'.Opens inferInstance
      (Opens.grothendieckTopology X'.toTopCat)
      (Sheaf.unitsAddSheaf X'.sheaf) hSheafify' hExt' 0) ≃+
    (@Sheaf.H X.Opens inferInstance
      (Opens.grothendieckTopology X.toTopCat)
      (Sheaf.unitsAddSheaf (presentationSheaf i))
      hSheafify hExt 0) :=
  (@Sheaf.H.equiv₀ X'.Opens inferInstance
      (Opens.grothendieckTopology X'.toTopCat) hSheafify' hExt'
      (Sheaf.unitsAddSheaf X'.sheaf) (⊤ : X'.Opens)
      isTerminalTop).trans
    ((presentationUnitsSectionsEquiv i).trans
      (@Sheaf.H.equiv₀ X.Opens inferInstance
        (Opens.grothendieckTopology X.toTopCat) hSheafify hExt
        (Sheaf.unitsAddSheaf (presentationSheaf i))
        (⊤ : X.Opens) isTerminalTop).symm)

/-- The canonical eight-object Picard cohomology row of a first-order
thickening, with ambient global units and Picard group in its displayed
positions. -/
noncomputable def picardCohomologySequence :
    ComposableArrows AddCommGrpCat.{u + 1} 7 :=
  let π := presentationProjection i
  let hzero := presentationKernel_isSquareZero i
  let hS := unitsShortComplex_shortExact π hzero
  let s := @SheafOfModules.RingedSite.KernelIdeal.picardCohomologySequence
    X.Opens inferInstance (Opens.grothendieckTopology X.toTopCat)
    (presentationSheaf i) X.sheaf hCommRingToRing hRingToAddCommGrp
    hForgetCommRing hWeakSheafify hLocallyBijective hExt
    (presentationSheaf_isLocallyRinged i) hXLocallyRinged π hzero hS
  let eUnits := presentationUnitsH0Equiv i
  let ePicard := presentationPicardEquiv i
  ((ComposableArrows.mk₅
      (AddCommGrpCat.ofHom eUnits.toAddMonoidHom ≫ s.map' 2 3)
      (s.map' 3 4)
      (s.map' 4 5 ≫ AddCommGrpCat.ofHom ePicard.symm.toAddMonoidHom)
      (AddCommGrpCat.ofHom ePicard.toAddMonoidHom ≫ s.map' 5 6)
      (s.map' 6 7)).precomp
    (s.map' 1 2 ≫ AddCommGrpCat.ofHom eUnits.symm.toAddMonoidHom)).precomp
      (s.map' 0 1)

/-- The Picard cohomology row of a first-order thickening is exact. -/
theorem picardCohomologySequence_exact :
    (picardCohomologySequence i).Exact := sorry

/-- The Picard arrow in the cohomology row is pullback along the original
first-order thickening. -/
theorem picardCohomologySequence_picardMap (x : X'.PicardGroup) :
    ((picardCohomologySequence i).map' 5 6).hom x =
      Scheme.Hom.picardPullback i x := sorry

end AlgebraicGeometry.IsFirstOrderThickening
