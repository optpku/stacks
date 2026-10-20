module
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
universe u v u' v'
namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (F : C ⥤ D) (V : C) (U : Over (F.obj V))

/-- Forget the slice structure in the pointwise inverse-image Kan index. -/
def overKanForget :
    CostructuredArrow (Over.post F).op (op U) ⥤ CostructuredArrow F.op (op U.left) where
  obj a := CostructuredArrow.mk (S := F.op) (Y := op a.left.unop.left) a.hom.unop.left.op
  map a := CostructuredArrow.homMk a.left.unop.left.op sorry
  map_id := sorry
  map_comp := sorry

variable [HasBinaryProducts C] [HasBinaryProducts D]
variable [PreservesLimitsOfShape (Discrete WalkingPair) F]

/-- Refine a Kan chart by the fixed slice object using an actual product. -/
def overKanRefine :
    CostructuredArrow F.op (op U.left) ⥤ CostructuredArrow (Over.post F).op (op U) where
  obj a :=
    CostructuredArrow.mk (S := (Over.post F).op)
      (Over.homMk (V := (Over.post F).obj (Over.mk
        (prod.snd : a.left.unop ⨯ V ⟶ V)))
        (prod.lift a.hom.unop U.hom ≫ (PreservesLimitPair.iso F a.left.unop V).inv) sorry).op
  map a := CostructuredArrow.homMk
    (Over.homMk (prod.map a.left.unop (𝟙 V)) sorry).op sorry
  map_id := sorry
  map_comp := sorry

/-- Product refinement is left adjoint to forgetting the slice structure. -/
def overKanAdjunction : overKanRefine F V U ⊣ overKanForget F V U :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun a b ↦
        { toFun := fun h ↦ CostructuredArrow.homMk
            (h.left.unop.left ≫ prod.fst).op sorry
          invFun := fun h ↦ CostructuredArrow.homMk
            (Over.homMk (prod.lift h.left.unop b.left.unop.hom) sorry).op sorry
          left_inv := sorry
          right_inv := sorry }
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

instance overKanForget_final : (overKanForget F V U).Final :=
  final_of_adjunction (overKanAdjunction F V U)

variable {A : Type*} [Category* A] (P : Cᵒᵖ ⥤ A)
variable [F.op.HasLeftKanExtension P] [F.op.HasPointwiseLeftKanExtension P]
variable [(Over.post F).op.HasLeftKanExtension ((Over.forget V).op ⋙ P)]
variable [(Over.post F).op.HasPointwiseLeftKanExtension ((Over.forget V).op ⋙ P)]

/-- The slice Kan extension uses the same colimit, through the actual final forgetful index. -/
def overKanObjIso :
    ((Over.post F).op.leftKanExtension ((Over.forget V).op ⋙ P)).obj (op U) ≅
      (F.op.leftKanExtension P).obj (op U.left) :=
  ((Over.post F).op.leftKanExtensionObjIsoColimit ((Over.forget V).op ⋙ P) (op U)) ≪≫
    (Final.colimitIso (overKanForget F V U)
      (CostructuredArrow.proj F.op (op U.left) ⋙ P)) ≪≫
    (F.op.leftKanExtensionObjIsoColimit P (op U.left)).symm

/-- The actual pointwise colimit comparisons form the slice Kan comparison. -/
def overKanIso :
    (Over.post F).op.leftKanExtension ((Over.forget V).op ⋙ P) ≅
      (Over.forget (F.obj V)).op ⋙ F.op.leftKanExtension P :=
  NatIso.ofComponents (fun U ↦ overKanObjIso F V U.unop P) (fun _ ↦ sorry)

end CategoryTheory.Functor
