module

public import ReasLib.Algebra.Category.DifferentialGraded.Homotopy.Preadditive
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.GradedHom
public import ReasLib.CategoryTheory.Functor.Equivalence

/-!
# DG-category of differential graded module sheaves

This leaf installs the canonical `ℤ`-linear DG-category structure on differential graded module
sheaves. It also compares the existing category of module homomorphisms with the closed
degree-zero category of the enrichment.
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

/-- Differential graded module sheaves over a fixed algebra form a `ℤ`-linear DG-category. -/
@[reducible]
instance differentialGradedCategory (𝒜 : DGA(𝒪)) :
    DifferentialGradedCategory ℤ (Mod(𝒜, d)) where
  Hom L M k := GradedHom 𝒜 L M k
  homAddCommGroup := fun _ _ _ ↦ inferInstance
  homModule := fun _ _ _ ↦ inferInstance
  «d» := fun k f ↦ gradedHomDifferential k f
  id := gradedHomId
  comp := fun {K L M} {i j} g f ↦ gradedHomComp g f
  d_sq := sorry
  d_id := sorry
  id_comp_hom := sorry
  comp_id_hom := sorry
  comp_assoc := sorry
  comp_add_left := sorry
  comp_add_right := sorry
  comp_smul_left := sorry
  comp_smul_right := sorry
  d_add := sorry
  d_smul := sorry
  d_comp := sorry

/-- The homogeneous morphisms in the DG-category are the right-linear graded maps. -/
@[simp]
theorem differentialGradedCategory_hom
    (𝒜 : DGA(𝒪)) (L M : Mod(𝒜, d)) (k : ℤ) :
    (L ⟶[k] M) = GradedHom 𝒜 L M k := sorry

/-- The enrichment differential is the standard graded-Hom differential. -/
@[simp]
theorem differentialGradedCategory_d
    {𝒜 : DGA(𝒪)} {L M : Mod(𝒜, d)} (k : ℤ)
    (f : GradedHom 𝒜 L M k) :
    (differentialGradedCategory 𝒜).d k f =
      gradedHomDifferential k f := sorry

/-- The enrichment identity is the degree-zero identity homogeneous map. -/
@[simp]
theorem differentialGradedCategory_id
    {𝒜 : DGA(𝒪)} (L : Mod(𝒜, d)) :
    (differentialGradedCategory 𝒜).id L = gradedHomId L := sorry

/-- Enriched composition is homogeneous composition. -/
@[simp]
theorem differentialGradedCategory_comp
    {𝒜 : DGA(𝒪)} {K L M : Mod(𝒜, d)} {i j : ℤ}
    (g : GradedHom 𝒜 L M j) (f : GradedHom 𝒜 K L i) :
    (differentialGradedCategory 𝒜).comp g f =
      gradedHomComp g f := sorry

/-- A closed degree-zero homogeneous map gives an ordinary differential graded module map. -/
def compHomToHom {𝒜 : DGA(𝒪)} {L M : Mod(𝒜, d)}
    (f : CompHom L M) : Hom L M where
  toCochainMap :=
    { f := fun n ↦
        f.val.hom n ≫
          eqToHom (congrArg M.toComplex.X (add_zero n))
      comm' := sorry }
  comm := sorry

/-- The cochain map underlying `compHomToHom` is computed from its homogeneous representative. -/
@[simp]
theorem compHomToHom_f
    {𝒜 : DGA(𝒪)} {L M : Mod(𝒜, d)}
    (f : CompHom L M) (n : ℤ) :
    (compHomToHom f).toCochainMap.f n =
      f.val.hom n ≫
        eqToHom (congrArg M.toComplex.X (add_zero n)) := sorry

/-- An ordinary differential graded module map gives a closed degree-zero homogeneous map. -/
def homToCompHom {𝒜 : DGA(𝒪)} {L M : Mod(𝒜, d)}
    (f : Hom L M) : CompHom L M :=
  ⟨
    { hom := fun n ↦
        f.toCochainMap.f n ≫
          eqToHom (congrArg M.toComplex.X (add_zero n).symm)
      comm := sorry },
    sorry⟩

/-- The homogeneous representative of `homToCompHom` is computed degreewise. -/
@[simp]
theorem homToCompHom_val_hom
    {𝒜 : DGA(𝒪)} {L M : Mod(𝒜, d)}
    (f : Hom L M) (n : ℤ) :
    (homToCompHom f).val.hom n =
      f.toCochainMap.f n ≫
        eqToHom (congrArg M.toComplex.X (add_zero n).symm) := sorry

namespace Hom

/-- Ordinary module maps and closed degree-zero homogeneous maps are additively equivalent. -/
def compEquiv {𝒜 : DGA(𝒪)} (L M : Mod(𝒜, d)) :
    Hom L M ≃+ CompHom L M where
  toFun := homToCompHom
  invFun := compHomToHom
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- The forward map of `Hom.compEquiv` is the closed homogeneous presentation. -/
@[simp]
theorem compEquiv_apply {𝒜 : DGA(𝒪)} (L M : Mod(𝒜, d)) (f : Hom L M) :
    compEquiv L M f = homToCompHom f := sorry

/-- The inverse map of `Hom.compEquiv` forgets a closed homogeneous presentation. -/
@[simp]
theorem compEquiv_symm_apply
    {𝒜 : DGA(𝒪)} (L M : Mod(𝒜, d)) (f : CompHom L M) :
    (compEquiv L M).symm f = compHomToHom f := sorry

end Hom

/-- Embed the ordinary differential graded module category into the closed degree-zero category. -/
def toComp (𝒜 : DGA(𝒪)) :
    Mod(𝒜, d) ⥤ Comp ℤ (Mod(𝒜, d)) where
  obj M := ⟨M⟩
  map f := homToCompHom f
  map_id := sorry
  map_comp := sorry

/-- `toComp` does not change the underlying module object. -/
@[simp]
theorem toComp_obj (𝒜 : DGA(𝒪)) (M : Mod(𝒜, d)) :
    (toComp 𝒜).obj M = ⟨M⟩ := sorry

/-- `toComp` presents an ordinary map as its closed degree-zero homogeneous map. -/
@[simp]
theorem toComp_map
    (𝒜 : DGA(𝒪)) {L M : Mod(𝒜, d)} (f : L ⟶ M) :
    (toComp 𝒜).map f = homToCompHom f := sorry

/-- The functor from ordinary module maps to closed degree-zero maps is additive. -/
instance toComp_additive (𝒜 : DGA(𝒪)) :
    (toComp 𝒜).Additive := sorry

/-- Forget a closed degree-zero presentation to an ordinary differential graded module map. -/
def fromComp (𝒜 : DGA(𝒪)) :
    Comp ℤ (Mod(𝒜, d)) ⥤ Mod(𝒜, d) where
  obj M := M.obj
  map f := compHomToHom f
  map_id := sorry
  map_comp := sorry

/-- `fromComp` recovers the underlying module object. -/
@[simp]
theorem fromComp_obj (𝒜 : DGA(𝒪)) (M : Comp ℤ (Mod(𝒜, d))) :
    (fromComp 𝒜).obj M = M.obj := sorry

/-- `fromComp` sends a closed homogeneous map to its ordinary module-map presentation. -/
@[simp]
theorem fromComp_map
    (𝒜 : DGA(𝒪)) {L M : Comp ℤ (Mod(𝒜, d))} (f : L ⟶ M) :
    (fromComp 𝒜).map f = compHomToHom f := sorry

/-- Forgetting the closed degree-zero presentation is additive. -/
instance fromComp_additive (𝒜 : DGA(𝒪)) :
    (fromComp 𝒜).Additive := sorry

/-- Explicit quasi-inverse data comparing ordinary module maps with closed degree-zero maps. -/
noncomputable def compQuasiInverse (𝒜 : DGA(𝒪)) :
    Functor.QuasiInverse (toComp 𝒜) where
  inverse := fromComp 𝒜
  unitIso := NatIso.ofComponents (fun M ↦ Iso.refl M) (fun _ ↦ sorry)
  counitIso := NatIso.ofComponents (fun M ↦ Iso.refl M) (fun _ ↦ sorry)

/-- The inverse stored in `compQuasiInverse` is the explicit forgetful functor `fromComp`. -/
@[simp]
theorem compQuasiInverse_inverse (𝒜 : DGA(𝒪)) :
    (compQuasiInverse 𝒜).inverse = fromComp 𝒜 := sorry

/-- The ordinary module category is explicitly equivalent to the closed degree-zero category. -/
noncomputable def compEquivalence (𝒜 : DGA(𝒪)) :
    Mod(𝒜, d) ≌ Comp ℤ (Mod(𝒜, d)) :=
  (compQuasiInverse 𝒜).adjointifyUnit

/-- The forward functor of `compEquivalence` is `toComp`. -/
@[simp]
theorem compEquivalence_functor (𝒜 : DGA(𝒪)) :
    (compEquivalence 𝒜).functor = toComp 𝒜 := sorry

/-- The inverse functor of `compEquivalence` is `fromComp`. -/
@[simp]
theorem compEquivalence_inverse (𝒜 : DGA(𝒪)) :
    (compEquivalence 𝒜).inverse = fromComp 𝒜 := sorry

/-- The ordinary module category and the closed degree-zero category are equivalent. -/
instance toComp_isEquivalence (𝒜 : DGA(𝒪)) :
    (toComp 𝒜).IsEquivalence := sorry

/-- Send an ordinary differential graded module and its morphisms directly to the DG homotopy
category. -/
def toK (𝒜 : DGA(𝒪)) :
    Mod(𝒜, d) ⥤ K ℤ Mod(𝒜, d) :=
  toComp 𝒜 ⋙ Comp.inKFunctor

/-- The direct functor to the DG homotopy category retains the underlying module object. -/
@[simp]
theorem toK_obj (𝒜 : DGA(𝒪)) (M : Mod(𝒜, d)) :
    (toK 𝒜).obj M = ⟨M⟩ := sorry

/-- The image in the DG homotopy category of a module morphism is its represented closed
degree-zero homotopy class. -/
@[simp]
theorem toK_map (𝒜 : DGA(𝒪)) {L M : Mod(𝒜, d)} (f : L ⟶ M) :
    (toK 𝒜).map f = (homToCompHom f).toHomotopyClass := sorry

/-- The direct functor from differential graded modules to their homotopy category is additive. -/
instance toK_additive (𝒜 : DGA(𝒪)) :
    (toK 𝒜).Additive := sorry

/-- Every DG homotopy class has a representative by an ordinary differential graded module
morphism. -/
instance toK_full (𝒜 : DGA(𝒪)) :
    (toK 𝒜).Full := sorry

/-- Every object of the DG homotopy category is represented by an ordinary differential graded
module. -/
instance toK_essSurj (𝒜 : DGA(𝒪)) :
    (toK 𝒜).EssSurj := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedModule
