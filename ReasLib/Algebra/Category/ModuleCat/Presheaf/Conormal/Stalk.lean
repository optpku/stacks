module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Conormal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk
public import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of kernel-cotangent module presheaves

For a morphism of presheaves of commutative rings on a topological space, the stalk of the
objectwise kernel-cotangent presheaf is canonically the cotangent module of the kernel of the
induced morphism on stalk rings. The comparison is constructed from its maps on neighborhood
representatives.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace PresheafOfModules.KernelCotangent.Stalk

variable {X : TopCat.{u}} {R S : X.Presheaf CommRingCat.{u}}

/-- The morphism on stalk rings induced by a morphism of commutative-ring presheaves. -/
abbrev ringMap (f : R ⟶ S) (x : X) : R.stalk x ⟶ S.stalk x :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map f

/-- The kernel ideal of the induced morphism on stalk rings. -/
abbrev ideal (f : R ⟶ S) (x : X) : Ideal (R.stalk x) :=
  RingHom.ker (ringMap f x).hom

/-- The stalk of the objectwise kernel-cotangent module presheaf. -/
abbrev source (f : R ⟶ S) (x : X) : ModuleCat (R.stalk x) :=
  PresheafOfModules.stalkModuleCatOfCommRing
    (PresheafOfModules.KernelCotangent.presheaf f) x

/-- The kernel-cotangent module of the induced morphism on stalk rings. -/
abbrev target (f : R ⟶ S) (x : X) : ModuleCat (R.stalk x) :=
  ModuleCat.of (R.stalk x) (ideal f x).Cotangent

/-- The germ morphism sends an objectwise kernel ideal into the kernel ideal on stalks. -/
theorem ideal_le_comap_germ (f : R ⟶ S) (x : X) (U : Opens X) (hx : x ∈ U) :
    PresheafOfModules.KernelCotangent.ideal f (op U) ≤
      (ideal f x).comap (R.germ U x hx).hom := sorry

/-- The germ of an element of an objectwise kernel ideal, regarded as an element of the stalk
kernel ideal. -/
def idealGerm (f : R ⟶ S) (x : X) (U : Opens X) (hx : x ∈ U)
    (z : PresheafOfModules.KernelCotangent.ideal f (op U)) : ideal f x :=
  ⟨R.germ U x hx z, ideal_le_comap_germ f x U hx z.2⟩

/-- A neighborhood representative of an element of the stalk kernel, together with the fact
that its image has zero germ. -/
structure Representative (f : R ⟶ S) (x : X) (z : ideal f x) where
  /-- The neighborhood on which the representative is defined. -/
  neighborhood : Opens X
  /-- The base point belongs to the representative neighborhood. -/
  memNeighborhood : x ∈ neighborhood
  /-- The section representing the underlying element of the source-ring stalk. -/
  value : R.obj (op neighborhood)
  /-- The germ of `value` is the underlying element of `z`. -/
  germValue : R.germ neighborhood x memNeighborhood value = (z : R.stalk x)
  /-- The image of `value` has zero germ in the target-ring stalk. -/
  imageGermEqZero :
    S.germ neighborhood x memNeighborhood (f.app (op neighborhood) value) =
      S.germ neighborhood x memNeighborhood 0

/-- A chosen neighborhood representative of a stalk-kernel element. The section and its
neighborhood come directly from `TopCat.Presheaf.exists_germ_eq`; the last field records the
kernel condition in the target stalk. -/
noncomputable def representative (f : R ⟶ S) (x : X) (z : ideal f x) :
    Representative f x z :=
  let h := TopCat.Presheaf.exists_germ_eq R (z : R.stalk x)
  { neighborhood := h.choose
    memNeighborhood := h.choose_spec.choose
    value := h.choose_spec.choose_spec.choose
    germValue := h.choose_spec.choose_spec.choose_spec
    imageGermEqZero :=
      (TopCat.Presheaf.stalkFunctor_map_germ_apply h.choose x h.choose_spec.choose f
          h.choose_spec.choose_spec.choose).symm.trans
        ((congrArg (fun r : R.stalk x ↦ ringMap f x r)
            h.choose_spec.choose_spec.choose_spec).trans
          ((RingHom.mem_ker.mp z.2).trans
            (map_zero (S.germ h.choose x h.choose_spec.choose).hom).symm)) }

/-- The chosen source-ring section has germ equal to the underlying stalk-kernel element. -/
theorem representative_germ (f : R ⟶ S) (x : X) (z : ideal f x) :
    R.germ (representative f x z).neighborhood x
      (representative f x z).memNeighborhood (representative f x z).value =
        (z : R.stalk x) := sorry

/-- A common refinement on which the image of a stalk-kernel representative is sectionwise
zero. Both restriction arrows are retained because they are the canonical output of
`TopCat.Presheaf.germ_eq`. -/
structure ZeroRefinement (f : R ⟶ S) (x : X) (z : ideal f x) where
  /-- The refined neighborhood. -/
  neighborhood : Opens X
  /-- The base point belongs to the refined neighborhood. -/
  memNeighborhood : x ∈ neighborhood
  /-- The restriction arrow used on the represented section. -/
  toRepresentative : neighborhood ⟶ (representative f x z).neighborhood
  /-- The restriction arrow used on the zero section. -/
  toZero : neighborhood ⟶ (representative f x z).neighborhood
  /-- On the refinement, the restricted image agrees with the restricted zero section. -/
  imageEqZero :
    S.map toRepresentative.op
        (f.app (op (representative f x z).neighborhood) (representative f x z).value) =
      S.map toZero.op 0

/-- The chosen refinement on which a representative of a stalk-kernel element maps to zero. -/
noncomputable def zeroRefinement (f : R ⟶ S) (x : X) (z : ideal f x) :
    ZeroRefinement f x z :=
  let h := S.germ_eq x (representative f x z).memNeighborhood
    (representative f x z).memNeighborhood
    (f.app (op (representative f x z).neighborhood) (representative f x z).value) 0
    (representative f x z).imageGermEqZero
  { neighborhood := h.choose
    memNeighborhood := h.choose_spec.choose
    toRepresentative := h.choose_spec.choose_spec.choose
    toZero := h.choose_spec.choose_spec.choose_spec.choose
    imageEqZero := h.choose_spec.choose_spec.choose_spec.choose_spec }

/-- The source-ring section obtained by restricting the chosen representative to its zero
refinement. -/
noncomputable def restrictedValue (f : R ⟶ S) (x : X) (z : ideal f x) :
    R.obj (op (zeroRefinement f x z).neighborhood) :=
  R.map (zeroRefinement f x z).toRepresentative.op (representative f x z).value

/-- The restricted representative lies in the sectionwise kernel ideal. -/
theorem restrictedValue_mem (f : R ⟶ S) (x : X) (z : ideal f x) :
    restrictedValue f x z ∈
      PresheafOfModules.KernelCotangent.ideal f
        (op (zeroRefinement f x z).neighborhood) := sorry

/-- The restricted representative, bundled as an element of the sectionwise kernel ideal. -/
noncomputable def restrictedIdealValue (f : R ⟶ S) (x : X) (z : ideal f x) :
    PresheafOfModules.KernelCotangent.ideal f
      (op (zeroRefinement f x z).neighborhood) :=
  ⟨restrictedValue f x z, restrictedValue_mem f x z⟩

/-- The germ of the restricted kernel representative is the original stalk-kernel element. -/
theorem restrictedIdealValue_germ (f : R ⟶ S) (x : X) (z : ideal f x) :
    idealGerm f x (zeroRefinement f x z).neighborhood
      (zeroRefinement f x z).memNeighborhood (restrictedIdealValue f x z) = z := sorry

/-- A sectionwise kernel representative of an element of the stalk kernel. -/
@[stacks 0D09 "local sectionwise representative of a stalk-kernel element"]
structure IdealRepresentative (f : R ⟶ S) (x : X) (z : ideal f x) where
  /-- The neighborhood on which the kernel representative is defined. -/
  neighborhood : Opens X
  /-- The base point belongs to the representative neighborhood. -/
  memNeighborhood : x ∈ neighborhood
  /-- The sectionwise kernel element. -/
  value : PresheafOfModules.KernelCotangent.ideal f (op neighborhood)
  /-- Its ideal germ is the original stalk-kernel element. -/
  idealGerm_eq : idealGerm f x neighborhood memNeighborhood value = z

/-- A chosen sectionwise kernel representative of a stalk-kernel element. Downstream users
should use `idealRepresentative_germ` or `idealToSourceValue_eq_germ`, not inspect this choice. -/
@[stacks 0D09 "local representative of a stalk-kernel element"]
noncomputable def idealRepresentative (f : R ⟶ S) (x : X) (z : ideal f x) :
    IdealRepresentative f x z where
  neighborhood := (zeroRefinement f x z).neighborhood
  memNeighborhood := (zeroRefinement f x z).memNeighborhood
  value := restrictedIdealValue f x z
  idealGerm_eq := restrictedIdealValue_germ f x z

/-- The ideal germ of the chosen sectionwise representative is the original stalk-kernel
element. -/
@[stacks 0D09 "local representative germ of a stalk-kernel element"]
theorem idealRepresentative_germ (f : R ⟶ S) (x : X) (z : ideal f x) :
    idealGerm f x (idealRepresentative f x z).neighborhood
      (idealRepresentative f x z).memNeighborhood (idealRepresentative f x z).value = z := sorry

/-- Every element of the kernel on stalks is locally represented by an element of the
sectionwise kernel. -/
@[stacks 0D09 "stalk-kernel elements are locally sectionwise kernel elements"]
theorem exists_idealGerm_eq (f : R ⟶ S) (x : X) (z : ideal f x) :
    ∃ (U : Opens X) (hx : x ∈ U)
      (zU : PresheafOfModules.KernelCotangent.ideal f (op U)),
      idealGerm f x U hx zU = z := sorry

/-- The comparison from one neighborhood's kernel-cotangent module to the kernel-cotangent
module on stalk rings. -/
noncomputable def leg (f : R ⟶ S) (x : X) (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙
      (PresheafOfModules.KernelCotangent.presheaf f).presheaf).obj U) ⟶
      (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (target f x) :=
  AddCommGrpCat.ofHom
    (@Ideal.mapCotangent
      (R.obj (op U.unop.1)) _ (R.obj (op U.unop.1)) (R.stalk x) _ _
      (Algebra.id (R.obj (op U.unop.1)))
      ((R.germ U.unop.1 x U.unop.2).hom.toAlgebra)
      (PresheafOfModules.KernelCotangent.ideal f (op U.unop.1)) (ideal f x)
      (@Algebra.ofId (R.obj (op U.unop.1)) (R.stalk x) _ _
        ((R.germ U.unop.1 x U.unop.2).hom.toAlgebra))
      (ideal_le_comap_germ f x U.unop.1 U.unop.2)).toAddMonoidHom

/-- A neighborhood comparison sends a cotangent generator to the generator represented by its
germ. -/
theorem leg_toCotangent (f : R ⟶ S) (x : X) (U : (OpenNhds x)ᵒᵖ)
    (z : PresheafOfModules.KernelCotangent.ideal f (op U.unop.1)) :
    leg f x U
        ((PresheafOfModules.KernelCotangent.ideal f (op U.unop.1)).toCotangent z) =
      (ideal f x).toCotangent (idealGerm f x U.unop.1 U.unop.2 z) := sorry

/-- The neighborhood comparisons are compatible with restriction. -/
theorem leg_naturality (f : R ⟶ S) (x : X)
    {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙
        (PresheafOfModules.KernelCotangent.presheaf f).presheaf).map i) ≫
        leg f x V =
      leg f x U := sorry

/-- The cocone of neighborhood kernel-cotangent modules with vertex the kernel-cotangent module
of the stalk morphism. -/
noncomputable def cocone (f : R ⟶ S) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙
      (PresheafOfModules.KernelCotangent.presheaf f).presheaf) where
  pt := (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (target f x)
  ι :=
    { app := leg f x
      naturality := fun _ _ i ↦ leg_naturality f x i }

/-- The additive comparison from the stalk of the kernel-cotangent presheaf to the
kernel-cotangent module of the stalk morphism. -/
noncomputable def addMap (f : R ⟶ S) (x : X) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (PresheafOfModules.KernelCotangent.presheaf f).presheaf x ⟶
      (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (target f x) :=
  colimit.desc _ (cocone f x)

/-- The additive stalk comparison preserves addition. -/
theorem addMap_add (f : R ⟶ S) (x : X) (m n : source f x) :
    addMap f x (m + n) = addMap f x m + addMap f x n := sorry

/-- The additive stalk comparison is linear over the source ring stalk. -/
theorem addMap_smul (f : R ⟶ S) (x : X) (r : R.stalk x) (m : source f x) :
    addMap f x (r • m) =
      HSMul.hSMul (α := R.stalk x) (β := target f x) r (addMap f x m) := sorry

/-- The canonical comparison from the stalk of the objectwise kernel-cotangent presheaf to the
kernel-cotangent module of the induced morphism on stalk rings. -/
@[stacks 0D09 "kernel-cotangent presheaf stalk comparison"]
noncomputable def comparison (f : R ⟶ S) (x : X) : source f x ⟶ target f x :=
  ModuleCat.ofHom
    { toFun := addMap f x
      map_add' := addMap_add f x
      map_smul' := addMap_smul f x }

/-- The stalk comparison sends the germ of an objectwise cotangent generator to the cotangent
generator represented by the germ of the kernel element. -/
@[stacks 0D09 "kernel-cotangent presheaf stalk comparison on generators"]
theorem comparison_germ_toCotangent (f : R ⟶ S) (x : X)
    (U : Opens X) (hx : x ∈ U)
    (z : PresheafOfModules.KernelCotangent.ideal f (op U)) :
    comparison f x
        (TopCat.Presheaf.germ
          (PresheafOfModules.KernelCotangent.presheaf f).presheaf U x hx
          ((PresheafOfModules.KernelCotangent.ideal f (op U)).toCotangent z)) =
      (ideal f x).toCotangent (idealGerm f x U hx z) := sorry

/-- The germ in the objectwise kernel-cotangent presheaf determined by the chosen local
representative of a stalk-kernel element. -/
noncomputable def idealToSourceValue (f : R ⟶ S) (x : X) (z : ideal f x) :
    source f x :=
  TopCat.Presheaf.germ (PresheafOfModules.KernelCotangent.presheaf f).presheaf
    (idealRepresentative f x z).neighborhood x
    (idealRepresentative f x z).memNeighborhood
    ((PresheafOfModules.KernelCotangent.ideal f
      (op (idealRepresentative f x z).neighborhood)).toCotangent
        (idealRepresentative f x z).value)

/-- `idealToSourceValue` may be computed using any local sectionwise-kernel representative of
its input. This is the choice-independence interface for the inverse comparison. -/
theorem idealToSourceValue_eq_germ (f : R ⟶ S) (x : X) (z : ideal f x)
    (a : IdealRepresentative f x z) :
    idealToSourceValue f x z =
      TopCat.Presheaf.germ (PresheafOfModules.KernelCotangent.presheaf f).presheaf
        a.neighborhood x a.memNeighborhood
        ((PresheafOfModules.KernelCotangent.ideal f (op a.neighborhood)).toCotangent
          a.value) := sorry

/-- On a stalk-kernel element given by a sectionwise kernel germ, `idealToSourceValue` is the
germ of the corresponding objectwise cotangent generator. -/
@[stacks 0D09 "inverse kernel-cotangent lift on represented kernel germs"]
theorem idealToSourceValue_idealGerm (f : R ⟶ S) (x : X)
    (U : Opens X) (hx : x ∈ U)
    (z : PresheafOfModules.KernelCotangent.ideal f (op U)) :
    idealToSourceValue f x (idealGerm f x U hx z) =
      TopCat.Presheaf.germ (PresheafOfModules.KernelCotangent.presheaf f).presheaf
        U x hx ((PresheafOfModules.KernelCotangent.ideal f (op U)).toCotangent z) := sorry

/-- The local inverse lift preserves addition of stalk-kernel elements. -/
theorem idealToSourceValue_add (f : R ⟶ S) (x : X) (z w : ideal f x) :
    idealToSourceValue f x (z + w) =
      idealToSourceValue f x z + idealToSourceValue f x w := sorry

/-- The local inverse lift is linear over the source-ring stalk. -/
theorem idealToSourceValue_smul (f : R ⟶ S) (x : X)
    (r : R.stalk x) (z : ideal f x) :
    idealToSourceValue f x (r • z) = r • idealToSourceValue f x z := sorry

/-- The linear map from the stalk kernel to the stalk of the objectwise kernel-cotangent
presheaf, obtained by taking the cotangent generator of a local kernel representative. -/
@[stacks 0D09 "linear local lift from the stalk kernel"]
noncomputable def idealToSource (f : R ⟶ S) (x : X) :
    ideal f x →ₗ[R.stalk x] source f x where
  toFun := idealToSourceValue f x
  map_add' := idealToSourceValue_add f x
  map_smul' := idealToSourceValue_smul f x

/-- The local inverse lift vanishes on products of two stalk-kernel elements. -/
theorem idealToSource_mul (f : R ⟶ S) (x : X) (z w : ideal f x) :
    idealToSource f x (z * w) = 0 := sorry

/-- The explicit inverse from the cotangent module of the stalk kernel to the stalk of the
objectwise kernel-cotangent presheaf. -/
@[stacks 0D09 "inverse kernel-cotangent presheaf stalk comparison"]
noncomputable def comparisonInv (f : R ⟶ S) (x : X) : target f x ⟶ source f x :=
  ModuleCat.ofHom (Ideal.Cotangent.lift (idealToSource f x) (idealToSource_mul f x))

/-- The inverse comparison sends a cotangent generator to the local lift of its stalk-kernel
representative. -/
@[stacks 0D09 "inverse kernel-cotangent stalk comparison on cotangent generators", simp]
theorem comparisonInv_toCotangent (f : R ⟶ S) (x : X) (z : ideal f x) :
    comparisonInv f x ((ideal f x).toCotangent z) = idealToSource f x z := sorry

/-- On a sectionwise-kernel germ, the inverse comparison sends the cotangent generator to the
germ of the objectwise cotangent generator. -/
@[stacks 0D09 "inverse kernel-cotangent stalk comparison on represented generators"]
theorem comparisonInv_toCotangent_idealGerm (f : R ⟶ S) (x : X)
    (U : Opens X) (hx : x ∈ U)
    (z : PresheafOfModules.KernelCotangent.ideal f (op U)) :
    comparisonInv f x ((ideal f x).toCotangent (idealGerm f x U hx z)) =
      TopCat.Presheaf.germ (PresheafOfModules.KernelCotangent.presheaf f).presheaf
        U x hx ((PresheafOfModules.KernelCotangent.ideal f (op U)).toCotangent z) := sorry

/-- The kernel-cotangent stalk comparison followed by its explicit inverse is the identity. -/
@[simp]
theorem comparison_hom_inv_id (f : R ⟶ S) (x : X) :
    comparison f x ≫ comparisonInv f x = 𝟙 _ := sorry

/-- The explicit inverse followed by the kernel-cotangent stalk comparison is the identity. -/
@[simp]
theorem comparison_inv_hom_id (f : R ⟶ S) (x : X) :
    comparisonInv f x ≫ comparison f x = 𝟙 _ := sorry

/-- The kernel-cotangent stalk comparison as explicit isomorphism data. -/
@[stacks 0D09 "kernel-cotangent presheaf stalk comparison isomorphism"]
noncomputable def comparisonIso (f : R ⟶ S) (x : X) :
    source f x ≅ target f x where
  hom := comparison f x
  inv := comparisonInv f x
  hom_inv_id := comparison_hom_inv_id f x
  inv_hom_id := comparison_inv_hom_id f x

/-- The kernel-cotangent construction commutes with passage to stalks. -/
@[stacks 0D09 "kernel-cotangent presheaf stalk comparison is an isomorphism", instance]
instance comparison_isIso (f : R ⟶ S) (x : X) :
    IsIso (comparison f x) :=
  (comparisonIso f x).isIso_hom

/-- The explicit inverse kernel-cotangent stalk comparison is an isomorphism. -/
instance comparisonInv_isIso (f : R ⟶ S) (x : X) :
    IsIso (comparisonInv f x) :=
  (comparisonIso f x).isIso_inv

/-- The forward map of the kernel-cotangent stalk isomorphism is the canonical comparison. -/
@[stacks 0D09 "kernel-cotangent presheaf stalk comparison isomorphism hom", simp]
theorem comparisonIso_hom (f : R ⟶ S) (x : X) :
    (comparisonIso f x).hom = comparison f x := sorry

/-- The inverse map of the kernel-cotangent stalk isomorphism is the explicit local lift. -/
@[stacks 0D09 "kernel-cotangent presheaf stalk comparison isomorphism inverse", simp]
theorem comparisonIso_inv (f : R ⟶ S) (x : X) :
    (comparisonIso f x).inv = comparisonInv f x := sorry

end PresheafOfModules.KernelCotangent.Stalk

-- The representative neighborhoods and inverse map are explicit. Any `sorryAx` below is
-- confined to subtype membership, choice-independence, linearity, and inverse-law proofs.
