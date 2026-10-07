module

public import ReasLib.Algebra.Category.DifferentialGraded.Homotopy.Preadditive
public import ReasLib.Algebra.Homology.DifferentialGradedModule.DifferentialGraded
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Preadditive
public import ReasLib.CategoryTheory.Functor.Equivalence

/-!
# Homotopies of Differential Graded Module Morphisms

This leaf identifies ordinary right-DG-module morphisms with closed degree-zero morphisms in the
canonical enrichment.  It also exposes a concrete degree-`-1` homotopy witness and the functors
from differential graded modules to the closed and homotopy categories.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}

/-- A closed degree-zero homogeneous map gives an ordinary differential graded module map. -/
def compHomToHom {L M : DifferentialGradedModule.{u, v} A}
    (f : CompHom L M) : L ⟶ M where
  hom n := ModuleCat.castLinearMap (congrArg M.X (add_zero n)) (f.val.1 n)
  comm_d := sorry
  comm_smul := sorry

/-- The degree-`n` component of the ordinary map underlying a closed homogeneous map. -/
@[simp] theorem compHomToHom_hom {L M : DifferentialGradedModule.{u, v} A}
    (f : CompHom L M) (n : ℤ) :
    (compHomToHom f).hom n =
      ModuleCat.castLinearMap (congrArg M.X (add_zero n)) (f.val.1 n) := sorry

/-- An ordinary differential graded module map gives a closed degree-zero homogeneous map. -/
def homToCompHom {L M : DifferentialGradedModule.{u, v} A}
    (f : L ⟶ M) : CompHom L M :=
  ⟨⟨fun n ↦ ModuleCat.castLinearMap (congrArg M.X (add_zero n).symm) (f.hom n), sorry⟩, sorry⟩

/-- The degree-`n` component of the closed homogeneous map associated to an ordinary map. -/
@[simp] theorem homToCompHom_val_apply {L M : DifferentialGradedModule.{u, v} A}
    (f : L ⟶ M) (n : ℤ) :
    (homToCompHom f).val.1 n =
      ModuleCat.castLinearMap (congrArg M.X (add_zero n).symm) (f.hom n) := sorry

namespace Hom

/-- Ordinary DG-module maps and closed degree-zero homogeneous maps are additively equivalent. -/
def compEquiv (L M : DifferentialGradedModule.{u, v} A) :
    (L ⟶ M) ≃+ CompHom L M where
  toFun := homToCompHom
  invFun := compHomToHom
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- The forward map of `compEquiv` is the closed homogeneous presentation. -/
@[simp] theorem compEquiv_apply (L M : DifferentialGradedModule.{u, v} A) (f : L ⟶ M) :
    compEquiv L M f = homToCompHom f := sorry

/-- The inverse map of `compEquiv` forgets a closed homogeneous presentation. -/
@[simp] theorem compEquiv_symm_apply (L M : DifferentialGradedModule.{u, v} A)
    (f : CompHom L M) :
    (compEquiv L M).symm f = compHomToHom f := sorry

end Hom

/-- Embed ordinary differential graded modules into the closed degree-zero category. -/
def toComp (A : CochainDGAlgebra R) :
    DifferentialGradedModule.{u, v} A ⥤ Comp R (DifferentialGradedModule A) where
  obj M := ⟨M⟩
  map f := homToCompHom f
  map_id := sorry
  map_comp := sorry

/-- `toComp` does not change the underlying differential graded module. -/
@[simp] theorem toComp_obj (A : CochainDGAlgebra R)
    (M : DifferentialGradedModule.{u, v} A) :
    (toComp A).obj M = ⟨M⟩ := sorry

/-- `toComp` presents an ordinary map as its closed degree-zero homogeneous map. -/
@[simp] theorem toComp_map (A : CochainDGAlgebra R)
    {L M : DifferentialGradedModule.{u, v} A} (f : L ⟶ M) :
    (toComp A).map f = homToCompHom f := sorry

/-- The closed degree-zero presentation preserves addition. -/
instance toComp_additive (A : CochainDGAlgebra R) : (toComp.{u, v} A).Additive := sorry

/-- Forget a closed degree-zero presentation to an ordinary DG-module map. -/
def fromComp (A : CochainDGAlgebra R) :
    Comp R (DifferentialGradedModule.{u, v} A) ⥤ DifferentialGradedModule A where
  obj M := M.obj
  map f := compHomToHom f
  map_id := sorry
  map_comp := sorry

/-- `fromComp` recovers the underlying differential graded module. -/
@[simp] theorem fromComp_obj (A : CochainDGAlgebra R)
    (M : Comp R (DifferentialGradedModule.{u, v} A)) :
    (fromComp A).obj M = M.obj := sorry

/-- `fromComp` forgets a closed homogeneous presentation degreewise. -/
@[simp] theorem fromComp_map (A : CochainDGAlgebra R)
    {L M : Comp R (DifferentialGradedModule.{u, v} A)} (f : L ⟶ M) :
    (fromComp A).map f = compHomToHom f := sorry

/-- Forgetting a closed degree-zero presentation preserves addition. -/
instance fromComp_additive (A : CochainDGAlgebra R) : (fromComp.{u, v} A).Additive := sorry

/-- Explicit quasi-inverse data for the closed degree-zero presentation. -/
noncomputable def compQuasiInverse (A : CochainDGAlgebra R) :
    Functor.QuasiInverse (toComp.{u, v} A) where
  inverse := fromComp A
  unitIso := NatIso.ofComponents (fun M ↦ Iso.refl M) (fun _ ↦ sorry)
  counitIso := NatIso.ofComponents (fun M ↦ Iso.refl M) (fun _ ↦ sorry)

/-- Ordinary DG modules are equivalent to the closed degree-zero category of their enrichment. -/
noncomputable def compEquivalence (A : CochainDGAlgebra R) :
    DifferentialGradedModule.{u, v} A ≌ Comp R (DifferentialGradedModule A) :=
  (compQuasiInverse A).adjointifyUnit

/-- The forward functor of `compEquivalence` is `toComp`. -/
@[simp] theorem compEquivalence_functor (A : CochainDGAlgebra R) :
    (compEquivalence.{u, v} A).functor = toComp A := sorry

/-- The inverse functor of `compEquivalence` is `fromComp`. -/
@[simp] theorem compEquivalence_inverse (A : CochainDGAlgebra R) :
    (compEquivalence.{u, v} A).inverse = fromComp A := sorry

/-- The closed degree-zero presentation is an equivalence. -/
instance toComp_isEquivalence (A : CochainDGAlgebra R) :
    (toComp.{u, v} A).IsEquivalence := sorry

/-- Send ordinary differential graded modules directly to their DG homotopy category. -/
def toK (A : CochainDGAlgebra R) :
    DifferentialGradedModule.{u, v} A ⥤ K R (DifferentialGradedModule A) :=
  toComp A ⋙ Comp.inKFunctor

/-- `toK` retains the underlying differential graded module object. -/
@[simp] theorem toK_obj (A : CochainDGAlgebra R)
    (M : DifferentialGradedModule.{u, v} A) :
    (toK A).obj M = ⟨M⟩ := sorry

/-- The image of an ordinary map in the DG homotopy category is its represented homotopy class. -/
@[simp] theorem toK_map (A : CochainDGAlgebra R)
    {L M : DifferentialGradedModule.{u, v} A} (f : L ⟶ M) :
    (toK A).map f = (homToCompHom f).toHomotopyClass := sorry

/-- The functor from ordinary DG modules to their homotopy category is additive. -/
instance toK_additive (A : CochainDGAlgebra R) : (toK.{u, v} A).Additive := sorry

/-- The functor from ordinary DG modules to their homotopy category is `R`-linear. -/
@[stacks 09KX "linearity of the canonical functor to the DG homotopy category"]
noncomputable instance toK_linear (A : CochainDGAlgebra R) :
    Functor.Linear R (toK.{u, v} A) := sorry

/-- Every DG homotopy class has an ordinary differential graded module representative. -/
instance toK_full (A : CochainDGAlgebra R) : (toK.{u, v} A).Full := sorry

/-- Every object of the DG homotopy category is represented by an ordinary DG module. -/
instance toK_essSurj (A : CochainDGAlgebra R) : (toK.{u, v} A).EssSurj := sorry

/-- A concrete homotopy between two ordinary differential graded module maps. -/
structure Homotopy {L M : DifferentialGradedModule.{u, v} A} (f g : L ⟶ M) where
  /-- The homogeneous degree-`-1` map carrying the homotopy. -/
  hom : GradedHom A L M (-1)
  /-- Its Hom differential is the difference of the two degree-zero maps. -/
  condition :
    (homToCompHom f).val - (homToCompHom g).val = gradedHomDifferential (-1) hom

namespace Homotopy

/-- An equality of ordinary DG-module maps gives the zero homotopy. -/
def ofEq {L M : DifferentialGradedModule.{u, v} A} {f g : L ⟶ M} (h : f = g) :
    Homotopy f g where
  hom := 0
  condition := sorry

/-- The homotopy attached to an equality has zero homogeneous component. -/
@[simp] theorem ofEq_hom {L M : DifferentialGradedModule.{u, v} A}
    {f g : L ⟶ M} (h : f = g) :
    (ofEq h).hom = 0 := sorry

/-- Every ordinary DG-module map is homotopic to itself. -/
def refl {L M : DifferentialGradedModule.{u, v} A} (f : L ⟶ M) : Homotopy f f :=
  ofEq rfl

/-- Reverse a concrete DG-module homotopy. -/
def symm {L M : DifferentialGradedModule.{u, v} A} {f g : L ⟶ M}
    (h : Homotopy f g) : Homotopy g f where
  hom := -h.hom
  condition := sorry

/-- Compose two concrete DG-module homotopies. -/
def trans {L M : DifferentialGradedModule.{u, v} A} {f g k : L ⟶ M}
    (h₁ : Homotopy f g) (h₂ : Homotopy g k) : Homotopy f k where
  hom := h₁.hom + h₂.hom
  condition := sorry

/-- A concrete DG-module homotopy gives the corresponding enriched homotopy relation. -/
theorem homotopic {L M : DifferentialGradedModule.{u, v} A} {f g : L ⟶ M}
    (h : Homotopy f g) :
    DifferentialGradedCategory.Homotopic L M (homToCompHom f) (homToCompHom g) := sorry

/-- Homotopic ordinary DG-module maps become equal in the DG homotopy category. -/
theorem toK_eq {L M : DifferentialGradedModule.{u, v} A} {f g : L ⟶ M}
    (h : Homotopy f g) :
    (toK A).map f = (toK A).map g := sorry

end Homotopy

/-- Enriched homotopy is equivalent to the mere existence of a concrete DG-module homotopy. -/
theorem homotopic_iff_nonempty_homotopy
    {L M : DifferentialGradedModule.{u, v} A} {f g : L ⟶ M} :
    DifferentialGradedCategory.Homotopic L M (homToCompHom f) (homToCompHom g) ↔
      Nonempty (Homotopy f g) := sorry

/-- Equality of represented morphisms in the DG homotopy category is equivalent to the existence
of a concrete homotopy. -/
theorem toK_map_eq_iff_nonempty_homotopy
    {L M : DifferentialGradedModule.{u, v} A} {f g : L ⟶ M} :
    (toK A).map f = (toK A).map g ↔ Nonempty (Homotopy f g) := sorry

#synth Functor.Linear R (toK.{u, v} A)

end DifferentialGradedModule
