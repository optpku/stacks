/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.GlobalSections.ConstantInteger
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DeRham.Wedge
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.HodgeFiltration
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GeneratedSubobject.AddCommGrp
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.Algebra.Category.Ring.Sheaf.Units.Map
import Mathlib.Algebra.Homology.Single

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf ComplexShape Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

variable {X S : Scheme.{u}}

/-- The additive sheaf underlying the degree-`i` term of the relative de Rham complex. -/
abbrev additiveTerm (f : X ⟶ S) (i : ℕ) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf
    (TopCat.Sheaf.ringSheafOfComm
      (RingedSpace.DeRham.coefficients f.toLRSHom.toShHom))).obj
    (RingedSpace.DeRham.term f.toLRSHom.toShHom i)

/-- The additive-term abbreviation is the underlying additive sheaf of the corresponding
relative de Rham term. -/
theorem additiveTerm_def (f : X ⟶ S) (i : ℕ) :
    additiveTerm f i =
      (SheafOfModules.toSheaf
        (TopCat.Sheaf.ringSheafOfComm
          (RingedSpace.DeRham.coefficients f.toLRSHom.toShHom))).obj
        (RingedSpace.DeRham.term f.toLRSHom.toShHom i) := sorry

/-- The local logarithmic `i`-form
`dlog(u₁) ∧ ⋯ ∧ dlog(uᵢ) = (∏ k, u k⁻¹) du₁ ∧ ⋯ ∧ duᵢ`. -/
noncomputable def logarithmicGenerator (f : X ⟶ S) (i : ℕ) (U : X.Opens)
    (a : Fin i → (Sheaf.unitsAddSheaf X.sheaf).1.obj (op U)) :
    (additiveTerm f i).1.obj (op U) :=
  SheafOfModules.RingedSite.DeRham.basic
    (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) i (op U)
    (∏ k, (Sheaf.unitsAddSheafUnit X.sheaf (a k))⁻¹).1
    (fun k ↦ Sheaf.unitsAddSheafValue X.sheaf (a k))

/-- The logarithmic generator is represented by the basic form whose coefficient is the
product of the inverse units. -/
theorem logarithmicGenerator_eq (f : X ⟶ S) (i : ℕ) (U : X.Opens)
    (a : Fin i → (Sheaf.unitsAddSheaf X.sheaf).1.obj (op U)) :
    logarithmicGenerator f i U a =
      SheafOfModules.RingedSite.DeRham.basic
        (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) i (op U)
        (∏ k, (Sheaf.unitsAddSheafUnit X.sheaf (a k))⁻¹).1
        (fun k ↦ Sheaf.unitsAddSheafValue X.sheaf (a k)) := sorry

namespace LogarithmicForms

/-- The constant-integer morphism whose image is the degree-zero logarithmic-form sheaf. -/
noncomputable def integerMap (f : X ⟶ S) :
    TopCat.Sheaf.constantIntegerSheaf X ⟶ additiveTerm f 0 :=
  (TopCat.Sheaf.constantIntegerHomEquivTopSection X (additiveTerm f 0)).symm
    (logarithmicGenerator f 0 ⊤ (fun k ↦ Fin.elim0 k))

/-- The sectionwise logarithmic differential before restricting its codomain to logarithmic
one-forms. -/
noncomputable def ambientDlogSection (f : X ⟶ S) (U : X.Opens) :
    (Sheaf.unitsAddSheaf X.sheaf).1.obj (op U) →
      (additiveTerm f 1).1.obj (op U) :=
  fun x ↦ logarithmicGenerator f 1 U (fun _ ↦ x)

/-- The ambient logarithmic differential preserves zero on sections. -/
theorem ambientDlogSection_zero (f : X ⟶ S) (U : X.Opens) :
    ambientDlogSection f U 0 = 0 := sorry

/-- The ambient logarithmic differential preserves addition on sections. -/
theorem ambientDlogSection_add (f : X ⟶ S) (U : X.Opens)
    (x y : (Sheaf.unitsAddSheaf X.sheaf).1.obj (op U)) :
    ambientDlogSection f U (x + y) =
      ambientDlogSection f U x + ambientDlogSection f U y := sorry

/-- The additive homomorphism underlying the ambient logarithmic differential on an open. -/
noncomputable def ambientDlogSectionHom (f : X ⟶ S) (U : X.Opens) :
    (Sheaf.unitsAddSheaf X.sheaf).1.obj (op U) →+
      (additiveTerm f 1).1.obj (op U) where
  toFun := ambientDlogSection f U
  map_zero' := ambientDlogSection_zero f U
  map_add' := ambientDlogSection_add f U

/-- The ambient logarithmic differential commutes with restriction of sections. -/
theorem ambientDlog_naturality (f : X ⟶ S) {U V : X.Opensᵒᵖ} (r : U ⟶ V) :
    (Sheaf.unitsAddSheaf X.sheaf).1.map r ≫
        AddCommGrpCat.ofHom (ambientDlogSectionHom f V.unop) =
      AddCommGrpCat.ofHom (ambientDlogSectionHom f U.unop) ≫
        (additiveTerm f 1).1.map r := sorry

/-- The canonical morphism `dlog : 𝒶_Xˣ ⟶ Ω¹_[X/S]` before taking its image. -/
noncomputable def ambientDlog (f : X ⟶ S) :
    Sheaf.unitsAddSheaf X.sheaf ⟶ additiveTerm f 1 :=
  ObjectProperty.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom (ambientDlogSectionHom f U.unop)
      naturality := fun {_ _} r ↦ ambientDlog_naturality f r }

end LogarithmicForms

/-- The additive subsheaf `Ωⁱ_[X/S,log]`: in degrees zero and one it is the canonical
image presentation, and in higher degrees it is generated by local logarithmic wedges. -/
noncomputable def logarithmicForms (f : X ⟶ S) :
    (i : ℕ) → Subobject (additiveTerm f i)
  | 0 => imageSubobject (LogarithmicForms.integerMap f)
  | 1 => imageSubobject (LogarithmicForms.ambientDlog f)
  | Nat.succ (Nat.succ i) =>
      AddCommGrpSubobject.generatedBySections (additiveTerm f (i + 2))
        (fun a : Σ U : X.Opens,
          Fin (i + 2) → (Sheaf.unitsAddSheaf X.sheaf).1.obj (op U) ↦ a.1)
        (fun a ↦ logarithmicGenerator f (i + 2) a.1 a.2)

namespace LogarithmicForms

/-- For positive degree, logarithmic forms are the least additive subsheaf containing the
local wedges `dlog(u₁) ∧ ⋯ ∧ dlog(uᵢ)`. -/
theorem positive_isLeast (f : X ⟶ S) (i : ℕ) (hi : 0 < i) :
    IsLeast
      {G : Subobject (additiveTerm f i) |
        AddCommGrpSubobject.ContainsSections G
          (fun a : Σ U : X.Opens,
            Fin i → (Sheaf.unitsAddSheaf X.sheaf).1.obj (op U) ↦ a.1)
          (fun a ↦ logarithmicGenerator f i a.1 a.2)}
      (logarithmicForms f i) := sorry

/-- Degree-zero logarithmic forms are the image of the constant-integer morphism. -/
theorem zero_eq_image (f : X ⟶ S) :
    logarithmicForms f 0 = imageSubobject (integerMap f) := sorry

/-- Degree-one logarithmic forms are the image of the ambient logarithmic differential. -/
theorem one_eq_image (f : X ⟶ S) :
    logarithmicForms f 1 = imageSubobject (ambientDlog f) := sorry

/-- The canonical logarithmic differential with codomain the degree-one logarithmic-form
subsheaf. -/
noncomputable def dlog (f : X ⟶ S) :
    Sheaf.unitsAddSheaf X.sheaf ⟶
      (logarithmicForms f 1 :
        Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  factorThruImageSubobject (ambientDlog f)

/-- The logarithmic differential followed by the subsheaf inclusion is the ambient
logarithmic differential. -/
theorem dlog_arrow (f : X ⟶ S) :
    dlog f ≫ (logarithmicForms f 1).arrow = ambientDlog f := sorry

/-- The relative de Rham complex after forgetting its module structure and retaining its
underlying sheaves of additive groups. -/
abbrev additiveComplex (f : X ⟶ S) :
    CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℕ :=
  ((SheafOfModules.toSheaf
      (TopCat.Sheaf.ringSheafOfComm
        (RingedSpace.DeRham.coefficients f.toLRSHom.toShHom))).mapHomologicalComplex (up ℕ)).obj
    (RingedSpace.DeRham.complex f.toLRSHom.toShHom)

/-- The additive complex has the additive sheaf underlying `Ωⁱ_[X/S]` in degree `i`. -/
theorem additiveComplex_X (f : X ⟶ S) (i : ℕ) :
    (additiveComplex f).X i = additiveTerm f i := sorry

/-- The relative de Rham differential vanishes on every logarithmic-form subsheaf. -/
theorem closed (f : X ⟶ S) (i k : ℕ) (hik : (up ℕ).Rel i k) :
    (logarithmicForms f i).arrow ≫ (additiveComplex f).d i k = 0 := sorry

/-- The canonical map from logarithmic `i`-forms placed in degree `i` to the relative de Rham
complex. -/
noncomputable def toDeRham (f : X ⟶ S) (i : ℕ) :
    (HomologicalComplex.single _ (up ℕ) i).obj
        (logarithmicForms f i :
          Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⟶
      additiveComplex f :=
  HomologicalComplex.mkHomFromSingle (logarithmicForms f i).arrow (closed f i)

/-- The degree-`i` component of `toDeRham` is the logarithmic-subsheaf inclusion. -/
theorem toDeRham_f (f : X ⟶ S) (i : ℕ) :
    (toDeRham f i).f i =
      (HomologicalComplex.singleObjXSelf (up ℕ) i
        (logarithmicForms f i :
          Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})).hom ≫
        (logarithmicForms f i).arrow := sorry

/-- The ambient wedge of two local logarithmic sections. -/
noncomputable def ambientWedgeSection (f : X ⟶ S) (i j : ℕ) (U : X.Opens)
    (x : (logarithmicForms f i :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U))
    (y : (logarithmicForms f j :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U)) :
    (additiveTerm f (i + j)).1.obj (op U) :=
  ((SheafOfModules.RingedSite.DeRham.wedgeComponent
      (RingedSpace.DeRham.structureMap f.toLRSHom.toShHom) i j).val.app (op U)).hom
    (SheafOfModules.RingedSite.tensorSection
      (RingedSpace.DeRham.coefficients f.toLRSHom.toShHom) (op U)
      (((logarithmicForms f i).arrow.hom.app (op U)).hom x)
      (((logarithmicForms f j).arrow.hom.app (op U)).hom y))

/-- The ambient logarithmic wedge preserves zero in its right argument. -/
theorem ambientWedgeSection_zero_right (f : X ⟶ S) (i j : ℕ) (U : X.Opens)
    (x : (logarithmicForms f i :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U)) :
    ambientWedgeSection f i j U x 0 = 0 := sorry

/-- The ambient logarithmic wedge preserves addition in its right argument. -/
theorem ambientWedgeSection_add_right (f : X ⟶ S) (i j : ℕ) (U : X.Opens)
    (x : (logarithmicForms f i :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U))
    (y y' : (logarithmicForms f j :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U)) :
    ambientWedgeSection f i j U x (y + y') =
      ambientWedgeSection f i j U x y + ambientWedgeSection f i j U x y' := sorry

/-- Ambient wedge with a fixed left logarithmic section, as an additive homomorphism. -/
noncomputable def ambientWedgeRight (f : X ⟶ S) (i j : ℕ) (U : X.Opens)
    (x : (logarithmicForms f i :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U)) :
    (logarithmicForms f j :
        Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U) →+
      (additiveTerm f (i + j)).1.obj (op U) where
  toFun := ambientWedgeSection f i j U x
  map_zero' := ambientWedgeSection_zero_right f i j U x
  map_add' := ambientWedgeSection_add_right f i j U x

/-- Ambient wedge with the zero left section is the zero additive homomorphism. -/
theorem ambientWedgeRight_zero (f : X ⟶ S) (i j : ℕ) (U : X.Opens) :
    ambientWedgeRight f i j U 0 = 0 := sorry

/-- Ambient wedge is additive in its left section. -/
theorem ambientWedgeRight_add (f : X ⟶ S) (i j : ℕ) (U : X.Opens)
    (x x' : (logarithmicForms f i :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U)) :
    ambientWedgeRight f i j U (x + x') =
      ambientWedgeRight f i j U x + ambientWedgeRight f i j U x' := sorry

/-- The sectionwise biadditive ambient wedge on logarithmic forms. -/
noncomputable def ambientWedgeMap (f : X ⟶ S) (i j : ℕ) (U : X.Opens) :
    (logarithmicForms f i :
        Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U) →+
      (logarithmicForms f j :
          Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U) →+
        (additiveTerm f (i + j)).1.obj (op U) where
  toFun := ambientWedgeRight f i j U
  map_zero' := ambientWedgeRight_zero f i j U
  map_add' := ambientWedgeRight_add f i j U

/-- The ambient logarithmic wedge commutes with restriction. -/
theorem ambientWedgeMap_naturality (f : X ⟶ S) (i j : ℕ)
    {U V : X.Opensᵒᵖ} (r : U ⟶ V)
    (x : (logarithmicForms f i :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj U)
    (y : (logarithmicForms f j :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj U) :
    ((additiveTerm f (i + j)).1.map r).hom (ambientWedgeMap f i j U.unop x y) =
      ambientWedgeMap f i j V.unop
        (((logarithmicForms f i :
          Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.map r).hom x)
        (((logarithmicForms f j :
          Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.map r).hom y) := sorry

/-- Every ambient wedge of logarithmic forms lies in the logarithmic-form subsheaf. -/
theorem ambientWedgeMap_mem (f : X ⟶ S) (i j : ℕ) (U : X.Opens)
    (x : (logarithmicForms f i :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U))
    (y : (logarithmicForms f j :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U)) :
    ∃ z : (logarithmicForms f (i + j) :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U),
      ((logarithmicForms f (i + j)).arrow.hom.app (op U)).hom z =
        ambientWedgeMap f i j U x y := sorry

/-- A logarithmic wedge map is explicit sectionwise biadditive ambient data, together with
the proof that its values lie in the logarithmic subsheaf and its restriction and ambient-wedge
laws. This avoids choosing representatives of sections of a categorical subobject. -/
structure WedgeMap (f : X ⟶ S) where
  /-- The ambient value of the sectionwise biadditive logarithmic wedge. -/
  map : ∀ (i j : ℕ) (U : X.Opens),
    (logarithmicForms f i :
        Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U) →+
      (logarithmicForms f j :
          Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U) →+
        (additiveTerm f (i + j)).1.obj (op U)
  /-- Every ambient value is represented by a section of the logarithmic subsheaf. -/
  mem : ∀ (i j : ℕ) (U : X.Opens)
    (x : (logarithmicForms f i :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U))
    (y : (logarithmicForms f j :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U)),
    ∃ z : (logarithmicForms f (i + j) :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U),
      ((logarithmicForms f (i + j)).arrow.hom.app (op U)).hom z = map i j U x y
  /-- The sectionwise maps commute with restriction. -/
  naturality : ∀ (i j : ℕ) {U V : X.Opensᵒᵖ} (r : U ⟶ V)
    (x : (logarithmicForms f i :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj U)
    (y : (logarithmicForms f j :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj U),
    ((additiveTerm f (i + j)).1.map r).hom (map i j U.unop x y) =
      map i j V.unop
        (((logarithmicForms f i :
          Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.map r).hom x)
        (((logarithmicForms f j :
          Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.map r).hom y)
  /-- The explicit ambient value is the ambient de Rham wedge. -/
  arrow : ∀ (i j : ℕ) (U : X.Opens)
    (x : (logarithmicForms f i :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U))
    (y : (logarithmicForms f j :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U)),
    map i j U x y = ambientWedgeMap f i j U x y

/-- The canonical logarithmic wedge, whose non-proof data is the explicit ambient wedge. -/
noncomputable def wedge (f : X ⟶ S) : WedgeMap f where
  map := ambientWedgeMap f
  mem := ambientWedgeMap_mem f
  naturality := ambientWedgeMap_naturality f
  arrow := fun _ _ _ _ _ ↦ rfl

/-- Logarithmic wedge maps are determined by their sectionwise map data. -/
@[ext]
theorem WedgeMap.ext {f : X ⟶ S} {W W' : WedgeMap f} (h : W.map = W'.map) :
    W = W' := sorry

/-- The explicit logarithmic wedge agrees with the ambient de Rham wedge after inclusion. -/
theorem wedge_arrow (f : X ⟶ S) (i j : ℕ) (U : X.Opens)
    (x : (logarithmicForms f i :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U))
    (y : (logarithmicForms f j :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U)) :
    (wedge f).map i j U x y = ambientWedgeMap f i j U x y := sorry

/-- Every logarithmic wedge map compatible with the ambient wedge is the canonical one. -/
theorem wedge_unique (f : X ⟶ S) (W : WedgeMap f) : W = wedge f := sorry

/-- Applying `toDeRham` to any logarithmic representative of the canonical wedge gives the
ambient wedge in the relative de Rham complex. -/
theorem toDeRham_wedge (f : X ⟶ S) (i j : ℕ) (U : X.Opens)
    (x : (logarithmicForms f i :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U))
    (y : (logarithmicForms f j :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U))
    (z : (logarithmicForms f (i + j) :
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).1.obj (op U))
    (hz : ((logarithmicForms f (i + j)).arrow.hom.app (op U)).hom z =
      (wedge f).map i j U x y) :
    ((((HomologicalComplex.singleObjXSelf (up ℕ) (i + j)
        (logarithmicForms f (i + j) :
          Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})).inv ≫
      (toDeRham f (i + j)).f (i + j)).hom.app (op U)).hom
        z) = ambientWedgeMap f i j U x y := sorry

end LogarithmicForms

end AlgebraicGeometry.Scheme.DeRham
