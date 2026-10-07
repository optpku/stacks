module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Triangulated
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Shift.Category
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Shift.GradedHom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

/-!
# Triangulated tensoring with a complex on a ringed site

The sectionwise tensor DG functor commutes with shifts because it sends the two homogeneous
identity maps relating a DG module and its shift to mutually inverse shifted cochain maps.  This
file records those maps explicitly and then passes to the standard homotopy category of complexes
of module sheaves.

The resulting functor is exact. Keeping the shift isomorphism here lets both derived constructions
and shifted-Hom APIs reuse the same data.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open CochainComplex.HomComplex
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace SheafOfModules.RingedSite.TensorWithObject

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- The standard homotopy category of complexes of modules on the fixed ringed site. -/
@[stacks 09LW "standard homotopy category of module complexes"]
abbrev TargetHomotopy :=
  HomotopyCategory.{max u v}
    (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)
    (ComplexShape.up ℤ)

/-- A closed homogeneous DG-module map remains a cocycle after tensoring with `K`. -/
@[stacks 09LW "tensoring closed maps gives cocycles"]
def mapCocycle (K : Complex (J := J) (O := O)) {M N : Modules K} {k : ℤ}
    (f : DifferentialGradedModule.ClosedGradedHom (endDGA K) M N k) :
    Cocycle (obj K M) (obj K N) k :=
  Cocycle.mk (map K f.1) (k + 1) rfl sorry

/-- The map from the shift of `M ⊗_(endDGA K) K` to `(M[k]) ⊗_(endDGA K) K`, obtained
by applying the tensor DG functor to the homogeneous identity `M ⟶ M[k]`. -/
@[stacks 09LW "tensor-shift map"]
def shiftHom (K : Complex (J := J) (O := O)) (M : Modules K) (k : ℤ) :
    (obj K M)⟦k⟧ ⟶ obj K (M[k]) :=
  (Cocycle.equivHomShift' k (-k) (neg_add_cancel k)).symm
    (mapCocycle K (DifferentialGradedModule.Shift.toGradedHom M k))

/-- The inverse map from `(M[k]) ⊗_(endDGA K) K` to the shift of
`M ⊗_(endDGA K) K`, obtained from the reverse homogeneous identity. -/
@[stacks 09LW "inverse tensor-shift map"]
def shiftInv (K : Complex (J := J) (O := O)) (M : Modules K) (k : ℤ) :
    obj K (M[k]) ⟶ (obj K M)⟦k⟧ :=
  Cocycle.equivHomShift.symm
    (mapCocycle K (DifferentialGradedModule.Shift.fromGradedHom M k))

/-- Tensoring with `K` commutes with the explicit shift of a right DG module. -/
@[stacks 09LW "tensor-shift isomorphism on complexes"]
def shiftIso (K : Complex (J := J) (O := O)) (M : Modules K) (k : ℤ) :
    (obj K M)⟦k⟧ ≅ obj K (M[k]) where
  hom := shiftHom K M k
  inv := shiftInv K M k
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The concrete functor from DG-module homotopy classes to the standard homotopy category of
complexes of module sheaves. -/
@[stacks 09LW "tensor functor on homotopy categories"]
def homotopyFunctor (K : Complex (J := J) (O := O)) :
    DifferentialGradedCategory.K ℤ (Modules K) ⥤
      TargetHomotopy (J := J) (O := O) :=
  (tensorFunctor K).mapK ⋙
    (CategoryTheory.CochainComplex.Enriched.toMathlib
      (A := ringedSiteModuleCategory.{u, v, max u v, max u v} J O))

/-- The pointwise shift comparison for the concrete tensor functor on standard homotopy
categories. -/
@[stacks 09LW "pointwise tensor-shift comparison"]
def homotopyShiftIsoApp (K : Complex (J := J) (O := O))
    (M : DifferentialGradedCategory.K ℤ (Modules K)) (k : ℤ) :
    ((DifferentialGradedModule.Shift.K.functor (endDGA K) k ⋙
        homotopyFunctor K).obj M) ≅
      ((homotopyFunctor K ⋙
        shiftFunctor (TargetHomotopy (J := J) (O := O)) k).obj M) :=
  (HomotopyCategory.quotient
      (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)
      (ComplexShape.up ℤ)).mapIso (shiftIso K M.obj k).symm ≪≫
    ((HomotopyCategory.quotient
      (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)
      (ComplexShape.up ℤ)).commShiftIso k).app (obj K M.obj)

/-- The pointwise tensor-shift comparisons are natural in a DG-module homotopy class. -/
@[reassoc, stacks 09LW "naturality of the tensor-shift comparison"]
theorem homotopyShiftIso_naturality (K : Complex (J := J) (O := O)) (k : ℤ)
    {M N : DifferentialGradedCategory.K ℤ (Modules K)} (f : M ⟶ N) :
    (DifferentialGradedModule.Shift.K.functor (endDGA K) k ⋙
        homotopyFunctor K).map f ≫ (homotopyShiftIsoApp K N k).hom =
      (homotopyShiftIsoApp K M k).hom ≫
        (homotopyFunctor K ⋙
          shiftFunctor (TargetHomotopy (J := J) (O := O)) k).map f := sorry

/-- Tensoring with `K` commutes naturally with the explicit shifts on its source homotopy
category and the canonical shifts on the target homotopy category. -/
@[stacks 09LW "natural tensor-shift comparison"]
def homotopyShiftIso (K : Complex (J := J) (O := O)) (k : ℤ) :
    DifferentialGradedModule.Shift.K.functor (endDGA K) k ⋙ homotopyFunctor K ≅
      homotopyFunctor K ⋙
        shiftFunctor (TargetHomotopy (J := J) (O := O)) k :=
  NatIso.ofComponents (fun M ↦ homotopyShiftIsoApp K M k)
    (fun f ↦ homotopyShiftIso_naturality K k f)

/-- Tensoring with `K` commutes with the canonical abstract shifts on homotopy categories. -/
@[stacks 09LW "canonical tensor-shift comparison"]
def homotopyCommShiftIso (K : Complex (J := J) (O := O)) (k : ℤ) :
    shiftFunctor (DifferentialGradedCategory.K ℤ (Modules K)) k ⋙ homotopyFunctor K ≅
      homotopyFunctor K ⋙
        shiftFunctor (TargetHomotopy (J := J) (O := O)) k :=
  (Functor.isoWhiskerRight
      (eqToIso (DifferentialGradedModule.Shift.K.shiftFunctor_eq (endDGA K) k))
      (homotopyFunctor K)).trans (homotopyShiftIso K k)

/-- The concrete tensor shift comparison agrees with the canonical zero-shift comparison. -/
theorem homotopyCommShiftIso_zero (K : Complex (J := J) (O := O)) :
    homotopyCommShiftIso K 0 = Functor.CommShift.isoZero (homotopyFunctor K) ℤ := sorry

/-- The concrete tensor shift comparison is coherent with addition of shifts. -/
theorem homotopyCommShiftIso_add (K : Complex (J := J) (O := O)) (i j : ℤ) :
    homotopyCommShiftIso K (i + j) =
      Functor.CommShift.isoAdd
        (homotopyCommShiftIso K i) (homotopyCommShiftIso K j) := sorry

/-- The homotopy functor induced by tensoring with `K` has canonical global shift
compatibility. -/
@[stacks 09LW "homotopy tensor commutes with shifts", reducible]
noncomputable def homotopyFunctor_commShift
    (K : Complex (J := J) (O := O)) : (homotopyFunctor K).CommShift ℤ where
  commShiftIso := homotopyCommShiftIso K
  commShiftIso_zero := homotopyCommShiftIso_zero K
  commShiftIso_add := homotopyCommShiftIso_add K

/-- Tensoring with `K` induces an exact functor from the homotopy category of right
`endDGA K`-modules to the homotopy category of complexes of module sheaves. -/
@[stacks 09LW "tensor with a complex is exact on homotopy categories"]
theorem homotopyFunctor_isTriangulated
    (K : Complex (J := J) (O := O)) :
    (homotopyFunctor K).IsTriangulatedWith (homotopyFunctor_commShift K) := sorry

end SheafOfModules.RingedSite.TensorWithObject
