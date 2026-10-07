module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.Shift.Induced
public import ReasLib.Algebra.Category.DifferentialGraded.Homotopy.FunctorCategory
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.DifferentialGraded

/-!
# Shifts of differential graded module sheaves

This leaf constructs the integer shift of a differential graded module sheaf from the canonical
shift of its underlying cochain complex. It then transports the shift to the closed degree-zero
category and to the DG homotopy category.
-/

@[expose] public section

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

-- Local declaration justification (parser boundary): this abbreviates the ambient category of
-- module sheaves and carries no local choice or instance.
local notation "ModO" => ringedSiteModuleCategory J 𝒪

namespace Shift

/-- The integer shift of a differential graded module sheaf. -/
def obj {𝒜 : DGA(𝒪)} (M : Mod(𝒜, d)) (k : ℤ) : Mod(𝒜, d) where
  toComplex := (CochainComplex.shiftFunctor ModO k).obj M.toComplex
  smul n m :=
    M.smul (n + k) m ≫
      eqToHom (congrArg M.toComplex.X (gradedHom_action_index n m k))
  smul_assoc := sorry
  one_smul := sorry
  d_smul := sorry

/-- The underlying complex of a shifted module is the shifted underlying complex. -/
@[simp]
theorem obj_toComplex {𝒜 : DGA(𝒪)} (M : Mod(𝒜, d)) (k : ℤ) :
    (obj M k).toComplex = (CochainComplex.shiftFunctor ModO k).obj M.toComplex := sorry

/-- The degree-`n` object of a shifted module is the degree-`n + k` object of the original. -/
@[simp]
theorem obj_X {𝒜 : DGA(𝒪)} (M : Mod(𝒜, d)) (k n : ℤ) :
    (obj M k).toComplex.X n = M.toComplex.X (n + k) := sorry

/-- The differential of a shifted module is the canonical signed shifted differential. -/
@[simp]
theorem obj_d {𝒜 : DGA(𝒪)} (M : Mod(𝒜, d)) (k i j : ℤ) :
    (obj M k).toComplex.d i j = k.negOnePow • M.toComplex.d (i + k) (j + k) := sorry

/-- The action on a shifted module is the original action followed by degree transport. -/
@[simp]
theorem obj_smul {𝒜 : DGA(𝒪)} (M : Mod(𝒜, d)) (k n m : ℤ) :
    (obj M k).smul n m =
      M.smul (n + k) m ≫
        eqToHom (congrArg M.toComplex.X (gradedHom_action_index n m k)) := sorry

/-- Shift a differential graded module morphism through the underlying cochain-complex shift. -/
def map {𝒜 : DGA(𝒪)} {M N : Mod(𝒜, d)} (f : M ⟶ N) (k : ℤ) :
    obj M k ⟶ obj N k where
  toCochainMap := (CochainComplex.shiftFunctor ModO k).map f.toCochainMap
  comm := sorry

/-- The underlying cochain map of a shifted module map is the shifted underlying cochain map. -/
@[simp]
theorem map_toCochainMap {𝒜 : DGA(𝒪)} {M N : Mod(𝒜, d)}
    (f : M ⟶ N) (k : ℤ) :
    (map f k).toCochainMap =
      (CochainComplex.shiftFunctor ModO k).map f.toCochainMap := sorry

/-- A shifted module map is evaluated in degree `n` by the original map in degree `n + k`. -/
@[simp]
theorem map_f {𝒜 : DGA(𝒪)} {M N : Mod(𝒜, d)}
    (f : M ⟶ N) (k n : ℤ) :
    (map f k).toCochainMap.f n = f.toCochainMap.f (n + k) := sorry

/-- Shifting by a fixed integer is an endofunctor on differential graded module sheaves. -/
def functor (𝒜 : DGA(𝒪)) (k : ℤ) : Mod(𝒜, d) ⥤ Mod(𝒜, d) where
  obj M := obj M k
  map f := map f k
  map_id := sorry
  map_comp := sorry

/-- The shift functor sends a module to its explicitly constructed shifted module. -/
@[simp]
theorem functor_obj (𝒜 : DGA(𝒪)) (M : Mod(𝒜, d)) (k : ℤ) :
    (functor 𝒜 k).obj M = obj M k := sorry

/-- The shift functor sends a map to its explicitly constructed shifted map. -/
@[simp]
theorem functor_map (𝒜 : DGA(𝒪)) {M N : Mod(𝒜, d)} (f : M ⟶ N) (k : ℤ) :
    (functor 𝒜 k).map f = map f k := sorry

/-- The component identifying the zero shift with the original module. -/
noncomputable def zeroApp {𝒜 : DGA(𝒪)} (M : Mod(𝒜, d)) : obj M 0 ≅ M where
  hom :=
    { toCochainMap := (CochainComplex.shiftFunctorZero' ModO 0 rfl).hom.app M.toComplex
      comm := sorry }
  inv :=
    { toCochainMap := (CochainComplex.shiftFunctorZero' ModO 0 rfl).inv.app M.toComplex
      comm := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying map of the forward zero-shift comparison is the cochain comparison. -/
@[simp]
theorem zeroApp_hom_toCochainMap {𝒜 : DGA(𝒪)} (M : Mod(𝒜, d)) :
    (zeroApp M).hom.toCochainMap =
      (CochainComplex.shiftFunctorZero' ModO 0 rfl).hom.app M.toComplex := sorry

/-- The underlying map of the inverse zero-shift comparison is the cochain comparison. -/
@[simp]
theorem zeroApp_inv_toCochainMap {𝒜 : DGA(𝒪)} (M : Mod(𝒜, d)) :
    (zeroApp M).inv.toCochainMap =
      (CochainComplex.shiftFunctorZero' ModO 0 rfl).inv.app M.toComplex := sorry

/-- The zero-shift comparison is natural in the differential graded module. -/
noncomputable def zero (𝒜 : DGA(𝒪)) : functor 𝒜 0 ≅ 𝟭 (Mod(𝒜, d)) :=
  NatIso.ofComponents (fun M ↦ zeroApp M) (fun _ ↦ sorry)

/-- The component comparing a shift by `a + b` with successive shifts by `a` and `b`. -/
noncomputable def addApp {𝒜 : DGA(𝒪)} (M : Mod(𝒜, d)) (a b : ℤ) :
    obj M (a + b) ≅ obj (obj M a) b where
  hom :=
    { toCochainMap :=
        (CochainComplex.shiftFunctorAdd' ModO a b (a + b) rfl).hom.app M.toComplex
      comm := sorry }
  inv :=
    { toCochainMap :=
        (CochainComplex.shiftFunctorAdd' ModO a b (a + b) rfl).inv.app M.toComplex
      comm := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward additive comparison has the canonical underlying cochain map. -/
@[simp]
theorem addApp_hom_toCochainMap {𝒜 : DGA(𝒪)} (M : Mod(𝒜, d)) (a b : ℤ) :
    (addApp M a b).hom.toCochainMap =
      (CochainComplex.shiftFunctorAdd' ModO a b (a + b) rfl).hom.app M.toComplex := sorry

/-- The inverse additive comparison has the canonical underlying cochain map. -/
@[simp]
theorem addApp_inv_toCochainMap {𝒜 : DGA(𝒪)} (M : Mod(𝒜, d)) (a b : ℤ) :
    (addApp M a b).inv.toCochainMap =
      (CochainComplex.shiftFunctorAdd' ModO a b (a + b) rfl).inv.app M.toComplex := sorry

/-- The additive shift comparison is natural in the differential graded module. -/
noncomputable def add (𝒜 : DGA(𝒪)) (a b : ℤ) :
    functor 𝒜 (a + b) ≅ functor 𝒜 a ⋙ functor 𝒜 b :=
  NatIso.ofComponents (fun M ↦ addApp M a b) (fun _ ↦ sorry)

/-- Coherent core data for the integer shifts of differential graded module sheaves. -/
noncomputable def core (𝒜 : DGA(𝒪)) : ShiftMkCore (Mod(𝒜, d)) ℤ where
  F := functor 𝒜
  zero := zero 𝒜
  add := add 𝒜
  assoc_hom_app := sorry
  zero_add_hom_app := sorry
  add_zero_hom_app := sorry

/-- Differential graded module sheaves carry their canonical integer shift. -/
@[implicit_reducible, stacks 0FS4]
noncomputable instance hasShift (𝒜 : DGA(𝒪)) : HasShift (Mod(𝒜, d)) ℤ :=
  hasShiftMk (Mod(𝒜, d)) ℤ (core 𝒜)

/-- The abstract shift functor is the explicit differential graded module shift functor. -/
theorem shiftFunctor_eq (𝒜 : DGA(𝒪)) (k : ℤ) :
    CategoryTheory.shiftFunctor (Mod(𝒜, d)) k = functor 𝒜 k := sorry

/-- Every integer shift of differential graded modules is additive. -/
instance shiftFunctor_additive (𝒜 : DGA(𝒪)) (k : ℤ) :
    (CategoryTheory.shiftFunctor (Mod(𝒜, d)) k).Additive := sorry

/-- Forgetting the action identifies the shift of a differential graded module with the
canonical shift of its underlying cochain complex. -/
noncomputable def forgetIso (𝒜 : DGA(𝒪)) (k : ℤ) :
    functor 𝒜 k ⋙ forgetToComplex 𝒜 ≅
      forgetToComplex 𝒜 ⋙ CochainComplex.shiftFunctor ModO k :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- The comparison between forgetting a shifted module and shifting its underlying complex is
the identity in every component. -/
@[simp]
theorem forgetIso_hom_app (𝒜 : DGA(𝒪)) (M : Mod(𝒜, d)) (k : ℤ) :
    (forgetIso 𝒜 k).hom.app M = 𝟙 ((obj M k).toComplex) := sorry

/-- The underlying-complex functor commutes with the canonical integer shifts. -/
noncomputable instance forgetCommShift (𝒜 : DGA(𝒪)) :
    (forgetToComplex 𝒜).CommShift ℤ where
  commShiftIso k := forgetIso 𝒜 k
  commShiftIso_zero := sorry
  commShiftIso_add := sorry

namespace Comp

/-- The explicit shift functor on the closed degree-zero category. -/
def functor (𝒜 : DGA(𝒪)) (k : ℤ) :
    DifferentialGradedCategory.Comp ℤ (Mod(𝒜, d)) ⥤
      DifferentialGradedCategory.Comp ℤ (Mod(𝒜, d)) where
  obj M := ⟨Shift.obj M.obj k⟩
  map f := homToCompHom (Shift.map (compHomToHom f) k)
  map_id := sorry
  map_comp := sorry

/-- The closed-category shift retains the explicitly shifted underlying module. -/
@[simp]
theorem functor_obj (𝒜 : DGA(𝒪))
    (M : DifferentialGradedCategory.Comp ℤ (Mod(𝒜, d))) (k : ℤ) :
    (functor 𝒜 k).obj M = ⟨Shift.obj M.obj k⟩ := sorry

/-- The closed-category shift maps a representative through the module shift. -/
@[simp]
theorem functor_map (𝒜 : DGA(𝒪))
    {M N : DifferentialGradedCategory.Comp ℤ (Mod(𝒜, d))} (f : M ⟶ N) (k : ℤ) :
    (functor 𝒜 k).map f = homToCompHom (Shift.map (compHomToHom f) k) := sorry

/-- The equivalence into closed degree-zero maps intertwines the explicit shifts. -/
noncomputable def inducedIso (𝒜 : DGA(𝒪)) (k : ℤ) :
    toComp 𝒜 ⋙ functor 𝒜 k ≅ Shift.functor 𝒜 k ⋙ toComp 𝒜 :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- The closed degree-zero category inherits its integer shift from module maps. -/
@[implicit_reducible]
noncomputable instance hasShift (𝒜 : DGA(𝒪)) :
    HasShift (DifferentialGradedCategory.Comp ℤ (Mod(𝒜, d))) ℤ :=
  HasShift.induced (toComp 𝒜) ℤ (functor 𝒜) (inducedIso 𝒜)

/-- The functor to closed degree-zero maps commutes with the induced integer shifts. -/
noncomputable instance toCompCommShift (𝒜 : DGA(𝒪)) : (toComp 𝒜).CommShift ℤ :=
  Functor.CommShift.ofInduced (toComp 𝒜) ℤ (functor 𝒜) (inducedIso 𝒜)

/-- The abstract closed-category shift is the explicit shift functor. -/
theorem shiftFunctor_eq (𝒜 : DGA(𝒪)) (k : ℤ) :
    CategoryTheory.shiftFunctor
        (DifferentialGradedCategory.Comp ℤ (Mod(𝒜, d))) k =
      functor 𝒜 k := sorry

/-- Every integer shift on the closed degree-zero category is additive. -/
instance shiftFunctor_additive (𝒜 : DGA(𝒪)) (k : ℤ) :
    (CategoryTheory.shiftFunctor
      (DifferentialGradedCategory.Comp ℤ (Mod(𝒜, d))) k).Additive := sorry

end Comp

namespace K

/-- Shifting a closed representative respects DG homotopy. -/
theorem map_sound {𝒜 : DGA(𝒪)} {M N : Mod(𝒜, d)}
    {f g : CompHom M N} (k : ℤ) (h : Homotopic M N f g) :
    (homToCompHom (Shift.map (compHomToHom f) k)).toHomotopyClass =
      (homToCompHom (Shift.map (compHomToHom g) k)).toHomotopyClass := sorry

/-- Shift a morphism in the DG homotopy category by shifting a closed representative. -/
def map {𝒜 : DGA(𝒪)}
    {M N : DifferentialGradedCategory.K ℤ (Mod(𝒜, d))} (f : M ⟶ N) (k : ℤ) :
    (⟨Shift.obj M.obj k⟩ : DifferentialGradedCategory.K ℤ (Mod(𝒜, d))) ⟶
      (⟨Shift.obj N.obj k⟩ : DifferentialGradedCategory.K ℤ (Mod(𝒜, d))) :=
  Quotient.lift
    (fun g : CompHom M.obj N.obj ↦
      (homToCompHom (Shift.map (compHomToHom g) k)).toHomotopyClass)
    (fun _ _ h ↦ map_sound k h)
    f

/-- The explicit shift functor on the DG homotopy category. -/
def functor (𝒜 : DGA(𝒪)) (k : ℤ) :
    DifferentialGradedCategory.K ℤ (Mod(𝒜, d)) ⥤
      DifferentialGradedCategory.K ℤ (Mod(𝒜, d)) where
  obj M := ⟨Shift.obj M.obj k⟩
  map f := map f k
  map_id := sorry
  map_comp := sorry

/-- The homotopy-category shift retains the explicitly shifted underlying module. -/
@[simp]
theorem functor_obj (𝒜 : DGA(𝒪))
    (M : DifferentialGradedCategory.K ℤ (Mod(𝒜, d))) (k : ℤ) :
    (functor 𝒜 k).obj M = ⟨Shift.obj M.obj k⟩ := sorry

/-- The homotopy-category shift of a represented map is represented by the shifted map. -/
@[simp]
theorem map_rep (𝒜 : DGA(𝒪)) {M N : Mod(𝒜, d)} (f : CompHom M N) (k : ℤ) :
    map f.toHomotopyClass k =
      (homToCompHom (Shift.map (compHomToHom f) k)).toHomotopyClass := sorry

/-- The quotient functor intertwines the explicit shifts. -/
noncomputable def inducedIso (𝒜 : DGA(𝒪)) (k : ℤ) :
    (DifferentialGradedCategory.Comp.inKFunctor :
        DifferentialGradedCategory.Comp ℤ (Mod(𝒜, d)) ⥤
          DifferentialGradedCategory.K ℤ (Mod(𝒜, d))) ⋙ functor 𝒜 k ≅
      CategoryTheory.shiftFunctor
          (DifferentialGradedCategory.Comp ℤ (Mod(𝒜, d))) k ⋙
        (DifferentialGradedCategory.Comp.inKFunctor :
          DifferentialGradedCategory.Comp ℤ (Mod(𝒜, d)) ⥤
            DifferentialGradedCategory.K ℤ (Mod(𝒜, d))) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- The DG homotopy category inherits its integer shift from closed maps. -/
@[implicit_reducible, stacks 0FS7]
noncomputable instance hasShift (𝒜 : DGA(𝒪)) :
    HasShift (DifferentialGradedCategory.K ℤ (Mod(𝒜, d))) ℤ :=
  HasShift.induced
    (DifferentialGradedCategory.Comp.inKFunctor :
      DifferentialGradedCategory.Comp ℤ (Mod(𝒜, d)) ⥤
        DifferentialGradedCategory.K ℤ (Mod(𝒜, d)))
    ℤ (functor 𝒜) (inducedIso 𝒜)

/-- The quotient functor to the DG homotopy category commutes with integer shifts. -/
noncomputable instance inKFunctorCommShift (𝒜 : DGA(𝒪)) :
    (DifferentialGradedCategory.Comp.inKFunctor :
      DifferentialGradedCategory.Comp ℤ (Mod(𝒜, d)) ⥤
        DifferentialGradedCategory.K ℤ (Mod(𝒜, d))).CommShift ℤ :=
  Functor.CommShift.ofInduced
    (DifferentialGradedCategory.Comp.inKFunctor :
      DifferentialGradedCategory.Comp ℤ (Mod(𝒜, d)) ⥤
        DifferentialGradedCategory.K ℤ (Mod(𝒜, d)))
    ℤ (functor 𝒜) (inducedIso 𝒜)

/-- The abstract homotopy-category shift is the explicit quotient shift functor. -/
@[stacks 0FS7]
theorem shiftFunctor_eq (𝒜 : DGA(𝒪)) (k : ℤ) :
    CategoryTheory.shiftFunctor
        (DifferentialGradedCategory.K ℤ (Mod(𝒜, d))) k =
      functor 𝒜 k := sorry

/-- Every integer shift on the DG homotopy category is additive. -/
instance shiftFunctor_additive (𝒜 : DGA(𝒪)) (k : ℤ) :
    (CategoryTheory.shiftFunctor
      (DifferentialGradedCategory.K ℤ (Mod(𝒜, d))) k).Additive := sorry

end K

/-- The direct functor from differential graded modules to their DG homotopy category commutes
with the canonical integer shifts. -/
noncomputable instance toKCommShift (𝒜 : DGA(𝒪)) :
    (toK 𝒜).CommShift ℤ :=
  Functor.CommShift.comp (toComp 𝒜)
    (DifferentialGradedCategory.Comp.inKFunctor :
      DifferentialGradedCategory.Comp ℤ (Mod(𝒜, d)) ⥤
        DifferentialGradedCategory.K ℤ (Mod(𝒜, d)))

end Shift

end

end SheafOfModules.RingedSite.DifferentialGradedModule
